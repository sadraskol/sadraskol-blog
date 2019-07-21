module Main where

import Prelude

import Sadraskol.Api (BlogDraft(..), BlogPost(..), Language(..), editDraft, getDrafts, getPosts, makePublic)
import CSS (renderedSheet)
import Data.Const (Const)
import Data.Formatter.DateTime (FormatterCommand(..), format)
import Data.List (List, fromFoldable)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.MediaType (MediaType(..))
import Effect (Effect)
import Effect.Aff (Aff, error, parallel, sequential, throwError)
import Effect.Aff.Class (class MonadAff)
import Foreign (unsafeToForeign)
import Halogen (ClassName(..), Component, ComponentHTML, HalogenM, defaultEval, get, liftAff, liftEffect, mkComponent, mkEval, modify_, put)
import Halogen.Aff (awaitLoad, runHalogenAff, selectElement)
import Halogen.HTML as H
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.VDom.Driver (runUI)
import Sadraskol.Layout (Page(..), layout)
import Sadraskol.Types (Action(..))
import Style (sadraskolStyle)
import Web.DOM.ParentNode (QuerySelector(..))
import Web.HTML (HTMLElement, window)
import Web.HTML.History (DocumentTitle(..), URL(..), pushState)
import Web.HTML.Window (history)

main :: Effect Unit
main = runHalogenAff do
  awaitLoad
  root <- selectElement' "#app"
  style <- selectElement' "head"
  _ <- runUI styleComponent unit style
  runUI sadraskolAdminUi unit root

styleComponent :: forall m. Component H.HTML (Const Void) Unit Void m
styleComponent =
  mkComponent
    { initialState: const unit
    , render: const $ H.style [ HP.type_ $ MediaType "text/css" ] [ H.text (fromMaybe "" $ renderedSheet sadraskolStyle) ]
    , eval: mkEval $ defaultEval
    }

type AllContent = { drafts :: Array BlogDraft, posts :: Array BlogPost }

data State
  = DraftOverview AllContent
  | PostOverview AllContent
  | EditingDraft BlogDraft
  | Splash
  | Loading State

sadraskolAdminUi :: forall f i o. Component H.HTML f i o Aff
sadraskolAdminUi = mkComponent
    { initialState: const Splash
    , render
    , eval: mkEval $ defaultEval { handleAction = handleAction
                                 , initialize = Just Init
                                 }
    }
  where
    render :: State -> ComponentHTML Action () Aff
    render Splash = H.div [ HP.class_ $ ClassName "container" ] [ H.text "Welcome..." ]
    render (Loading before) = render before
    render (DraftOverview all) = H.div_ [ layout Drafts, H.div [ HP.class_ $ ClassName "container" ] [ draftOverview all ] ]
    render (PostOverview all) = H.div_ [ layout Posts, H.div [ HP.class_ $ ClassName "container" ] [ postOverview all ] ]
    render (EditingDraft draft) = H.div_ [ layout Drafts, H.div [ HP.class_ $ ClassName "container" ] [ editingDraft draft ] ]

    handleAction :: Action -> HalogenM State Action () o Aff Unit
    handleAction Init = do
      content <- liftAff $ sequential ado
        parDrafts <- parallel getDrafts
        parPosts <- parallel getPosts
        in {drafts: parDrafts, posts: parPosts}
      setTitleAndUrl (DocumentTitle "Drafts") (URL "/drafts")
      put (DraftOverview content)
    handleAction (MakePublic draft) = do
      before <- get
      put (Loading before)
      _ <- liftAff $ makePublic draft
      drafts <- liftAff getDrafts
      modify_ $ \a -> case a of
        Loading (DraftOverview { posts }) -> DraftOverview { drafts, posts }
        Loading other -> other
        any -> any
    handleAction GoToPosts = do
      currentState <- get
      case currentState of
        DraftOverview content -> do
          setTitleAndUrl (DocumentTitle "Posts") (URL "/posts")
          put $ PostOverview content
        PostOverview _ -> pure unit
        any -> do
          content <- liftAff $ sequential ado
            parDrafts <- parallel getDrafts
            parPosts <- parallel getPosts
            in {drafts: parDrafts, posts: parPosts}
          setTitleAndUrl (DocumentTitle "Posts") (URL "/posts")
          put (PostOverview content)
    handleAction GoToDrafts = do
      currentState <- get
      case currentState of
        PostOverview content -> do
          setTitleAndUrl (DocumentTitle "Drafts") (URL "/drafts")
          put $ DraftOverview content
        DraftOverview _ -> pure unit
        any -> do
          content <- liftAff $ sequential ado
            parDrafts <- parallel getDrafts
            parPosts <- parallel getPosts
            in {drafts: parDrafts, posts: parPosts}
          setTitleAndUrl (DocumentTitle "Drafts") (URL "/drafts")
          put (DraftOverview content)
    handleAction (GoEditDraft draft@(BlogDraft d)) = do
      setTitleAndUrl (DocumentTitle d.title) (URL $ "/drafts/" <> d.title)
      put $ EditingDraft draft
    handleAction CloseDraftEditing = do
      content <- liftAff $ sequential ado
        parDrafts <- parallel getDrafts
        parPosts <- parallel getPosts
        in {drafts: parDrafts, posts: parPosts}
      setTitleAndUrl (DocumentTitle "Drafts") (URL "/drafts")
      put (DraftOverview content)
    handleAction (EditNewDraft draft@(BlogDraft d)) = do
      editedDraft <- liftAff $ editDraft draft ({ language: d.language, title: d.title, markdown_content: d.markdown_content })
      put $ EditingDraft editedDraft
    handleAction (UpdateDraftContent c) = do
      modify_ \a -> case a of
        EditingDraft (BlogDraft d) -> EditingDraft $ BlogDraft d { markdown_content = c }
        any -> any
    handleAction (UpdateDraftTitle t) = do
      modify_ \a -> case a of
        EditingDraft (BlogDraft d) -> EditingDraft $ BlogDraft d { title = t }
        any -> any
    handleAction (UpdateDraftLanguage l) = do
      modify_ \a -> case a of
        EditingDraft (BlogDraft d) -> EditingDraft $ BlogDraft d { language = l }
        any -> any

setTitleAndUrl :: forall m. MonadAff m => DocumentTitle -> URL -> m Unit
setTitleAndUrl title url = liftEffect do
  hist <- (history =<< window)
  pushState (unsafeToForeign "") title url hist

draftOverview :: forall a. AllContent -> H.HTML a Action
draftOverview all = H.div_ $ draftItem <$> all.drafts

draftItem :: forall a. BlogDraft -> H.HTML a Action
draftItem draft@(BlogDraft d) = H.div [ HP.class_ $ ClassName "draft-item" ]
  [ H.div_ [ H.strong_ [ H.text d.title ] ]
  , H.ul [ HP.class_ $ ClassName "draft-item__actions" ]
    [ H.li [ HP.class_ $ ClassName "draft-item__actions__item" ] [ H.a [ HP.href "#", HE.onClick (const $ Just $ GoEditDraft draft) ] [ H.text "Edit" ] ]
    , H.li [ HP.class_ $ ClassName "draft-item__actions__item" ] [ H.a [ HP.href "#" ] [ H.text "Publish" ] ]
    , H.li [ HP.class_ $ ClassName "draft-item__actions__item" ] [
        case d.current_slug of
          Nothing -> H.a [ HP.href "#", HE.onClick (\_ -> Just $ MakePublic draft) ] [ H.text "Make Public" ]
          Just slug -> H.a [ HP.href slug ] [ H.text "Preview" ]
      ]
    ]
  ]

opposite :: Language -> Language
opposite Fr = En
opposite En = Fr

editingDraft :: forall a. BlogDraft ->  H.HTML a Action
editingDraft draft@(BlogDraft d) = H.div_
  [ H.div [ HP.class_ $ ClassName "editor-header" ]
    [ H.a [ HP.href "#", HE.onClick (const $ Just CloseDraftEditing) ] [ H.text "Close" ]
    , H.a [ HP.href "#", HE.onClick (const $ Just $ EditNewDraft draft) ] [ H.text "Save" ]
    , H.div [ HP.class_ $ ClassName "editor-header__right" ]
      [ H.select [ HP.class_ $ ClassName "editor-language__select", HE.onChange (const $ Just $ UpdateDraftLanguage $ opposite d.language) ]
        [ H.option
          [ HP.class_ $ ClassName "editor-language__option"
          , HP.selected $ d.language == En
          ] [ H.text "English" ]
        , H.option
          [ HP.class_ $ ClassName "editor-language__option"
          , HP.selected $ d.language == Fr
          ] [ H.text "Français" ]
        ]
      ]
    ]
  , H.div [ HP.class_ $ ClassName "editor" ]
    [ H.div [ HP.class_ $ ClassName "editor-title" ]
      [ H.input
        [ HP.class_ $ ClassName "editor-title__input"
        , HP.value d.title
        , HP.autocomplete false
        , HE.onValueInput (Just <<< UpdateDraftTitle)
        ]
      ]
    , H.div [ HP.class_ $ ClassName "editor-content" ]
      [ H.textarea
        [ HP.class_ $ ClassName "editor-content__textarea"
        , HP.rows 150
        , HP.value d.markdown_content
        , HE.onValueInput (Just <<< UpdateDraftContent)
        ]
      ]
    ]
  ]

postOverview :: forall a. AllContent -> H.HTML a Action
postOverview all = H.div_ $ postItem <$> all.posts

formatter :: List FormatterCommand
formatter = fromFoldable
  [ MonthFull
  , Placeholder " "
  , DayOfWeek
  , Placeholder ", "
  , YearFull
  , Placeholder " "
  , Hours12
  , Placeholder ":"
  , MinutesTwoDigits
  , Meridiem
  ]

showPublicationDate :: BlogPost -> String
showPublicationDate (BlogPost p) = fromMaybe "???" $ (format formatter) <$> p.publication_date

postItem :: forall a. BlogPost -> H.HTML a Action
postItem post@(BlogPost p) = H.div [ HP.class_ $ ClassName "post-item" ]
  [ H.div_ [ H.strong_ [ H.text p.title ] ]
  , H.ul [ HP.class_ $ ClassName "post-item__actions" ]
    [ H.li [ HP.class_ $ ClassName "post-item__actions__item" ] [ H.text $ showPublicationDate post ]
    , H.li [ HP.class_ $ ClassName "post-item__actions__item" ] [ H.a [ HP.href "#" ] [ H.text "Edit" ] ]
    , H.li [ HP.class_ $ ClassName "post-item__actions__item" ] [ H.a [ HP.href p.links.view ] [ H.text "View" ] ]
    , H.li [ HP.class_ $ ClassName "post-item__actions__item" ] [ H.a [ HP.href "#" ] [ H.text "Share" ] ]
    ]
  ]

selectElement' :: String -> Aff HTMLElement
selectElement' selector = do
  maybeEl <- selectElement $ QuerySelector selector
  fromMaybe (throwError $ error $ (selector <> " was not found")) (pure <$> maybeEl)
