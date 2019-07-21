module Sadraskol.Layout where

import Prelude

import Data.Maybe (Maybe(..))
import Halogen.HTML as H
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Sadraskol.Types (Action(..))

data Page
  = Posts
  | Drafts

derive instance eqPage :: Eq Page

layout :: forall a. Page -> H.HTML a Action
layout page = H.header [ HP.class_ $ H.ClassName "container" ]
  [ H.h2_ [ H.text "Sadraskol" ]
  , H.ul [ HP.class_ $ H.ClassName "overview-menu" ]
    [ H.li [ HP.classes $ H.ClassName <$> [ "overview-menu__item" ] <> (isActive Drafts page) ]
      [ H.a
        [ HE.onClick (const $ Just GoToDrafts) ]
        [ H.text "Drafts" ]
      ]
    , H.li [ HP.classes $ H.ClassName <$> [ "overview-menu__item" ] <> (isActive Posts page) ]
      [ H.a
        [ HE.onClick (const $ Just GoToPosts) ]
        [ H.text $ "Posts" ]
      ]
    ]
  ]

isActive :: Page -> Page -> Array String
isActive page other
  | page == other = [ "is-active" ]
  | otherwise = []