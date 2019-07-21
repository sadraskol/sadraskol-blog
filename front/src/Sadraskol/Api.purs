module Sadraskol.Api where

import Prelude

import Affjax (defaultRequest)
import Affjax as AJ
import Affjax.RequestBody (RequestBody(..))
import Affjax.RequestBody as RequestBody
import Affjax.RequestHeader (RequestHeader(..))
import Affjax.ResponseFormat (string)
import Data.DateTime (DateTime)
import Data.Either (Either(..))
import Data.HTTP.Method (Method(..))
import Data.JSDate (parse, toDateTime)
import Data.List.Types (NonEmptyList)
import Data.Maybe (Maybe(..))
import Data.MediaType.Common (applicationJSON)
import Data.Traversable (traverse)
import Effect (Effect)
import Effect.Aff (Aff, throwError, error)
import Effect.Class (liftEffect)
import Foreign (ForeignError(..), fail)
import Simple.JSON (class ReadForeign, class WriteForeign, readImpl, readJSON, writeImpl, writeJSON)

data Language = Fr | En

derive instance eqLanguage :: Eq Language

instance showLanguage :: Show Language where
  show Fr = "fr"
  show En = "en"

instance readForeignLanguage :: ReadForeign Language where
  readImpl f = do
    str <- readImpl f
    case str of
      "fr" -> pure Fr
      "en" -> pure En
      lang -> fail $ ForeignError $ "unknown language " <> lang

instance writeForeignLanguage :: WriteForeign Language where
  writeImpl Fr = writeImpl "fr"
  writeImpl En = writeImpl "en"

type BlogDraftLinks =
  { self :: String
  , make_public :: String
  , publish :: String
  }

type BlogDraftRaw =
  { title :: String
  , markdown_content :: String
  , language :: Language
  , current_slug :: Maybe String
  , links :: BlogDraftLinks
  }

type BlogPostLinks =
  { self :: String
  , view :: String
  }

type BlogPostRaw =
  { title :: String
  , markdown_content :: String
  , language :: Language
  , publication_date :: String
  , current_slug :: String
  , links :: BlogPostLinks
  }

type SubmitDraft =
  { language :: Language
  , title :: String
  , markdown_content :: String
  }

type EditPost =
  { language :: String
  , title :: String
  , markdown_content :: String
  }

newtype BlogPost = BlogPost
  { title :: String
  , markdown_content :: String
  , language :: Language
  , publication_date :: Maybe DateTime
  , current_slug :: String
  , links :: BlogPostLinks
  }

parseBlogPostToDraft :: BlogPostRaw -> Effect BlogPost
parseBlogPostToDraft raw = do
  jsDate <- parse raw.publication_date
  pure $ BlogPost
    { title: raw.title
    , markdown_content: raw.markdown_content
    , language: raw.language
    , publication_date: toDateTime jsDate
    , current_slug: raw.current_slug
    , links: raw.links
    }

newtype BlogDraft = BlogDraft BlogDraftRaw

class Resource a where
  showing :: a -> String

instance resourceBlogDraft :: Resource BlogDraft where
  showing :: BlogDraft -> String
  showing (BlogDraft draft) = show draft

instance resourceBlogPost :: Resource BlogPost where
  showing :: BlogPost -> String
  showing (BlogPost post) = show post

defaultRequestParse :: forall a. ReadForeign a => AJ.Response (Either AJ.ResponseFormatError String) -> Aff a
defaultRequestParse res = case res.body of
  Left err -> throwError $ error $ "Could not parse body: " <> AJ.printResponseFormatError err
  Right body -> case (readJSON body :: Either (NonEmptyList ForeignError) a) of
    Left err -> throwError $ error $ "Could not parse json: " <> show err
    Right json -> pure json

-- actual requests

submitDraft :: SubmitDraft -> Aff BlogDraft
submitDraft req = do
  res <- AJ.post string "/api/drafts" (RequestBody.string $ writeJSON req)
  BlogDraft <$> defaultRequestParse res

editDraft :: BlogDraft -> SubmitDraft -> Aff BlogDraft
editDraft (BlogDraft draft) req = do
  res <- AJ.request $ defaultRequest
    { method = Left PATCH
    , url = draft.links.self
    , content = Just $ RequestBody.string $ writeJSON req
    , headers = [ ContentType applicationJSON ]
    , responseFormat = string
    }
  BlogDraft <$> defaultRequestParse res

getDrafts :: Aff (Array BlogDraft)
getDrafts = do
  res <- AJ.get string "/api/drafts"
  (map <<< map) BlogDraft (defaultRequestParse res)

getPosts :: Aff (Array BlogPost)
getPosts = do
  res <- AJ.get string "/api/posts"
  parsedJson <- defaultRequestParse res
  traverse (liftEffect <<< parseBlogPostToDraft) parsedJson

getSelf :: BlogDraft -> Aff BlogDraft
getSelf (BlogDraft draft) = do
  res <- AJ.get string draft.links.self
  BlogDraft <$> defaultRequestParse res

makePublic :: BlogDraft -> Aff BlogDraft
makePublic (BlogDraft draft) = do
  res <- AJ.post string draft.links.make_public (RequestBody.string "")
  BlogDraft <$> defaultRequestParse res

publish :: BlogDraft -> SubmitDraft -> Aff BlogPost
publish (BlogDraft draft) req = do
  res <- AJ.post string draft.links.publish (RequestBody.string $ writeJSON req)
  parsedJson <- defaultRequestParse res
  liftEffect $ parseBlogPostToDraft parsedJson
