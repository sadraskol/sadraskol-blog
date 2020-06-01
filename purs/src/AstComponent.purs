module AstComponent where

import Ast
import Prelude

import Data.Maybe (Maybe(..))
import Data.NonEmpty ((:|))
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE

type State = AST

data Action = Insert

component :: forall q i o m. H.Component HH.HTML q i o m
component =
  H.mkComponent
    { initialState
    , render
    , eval: H.mkEval $ H.defaultEval { handleAction = handleAction }
    }

initialState :: forall i. i -> State
initialState _ = empty

render :: forall m. State -> H.ComponentHTML Action () m
render state =
    HH.div [] [ HH.div [] $ renderState state, HH.button [ HE.onClick \_ -> Just Insert ] [ HH.text "Insert" ] ]

renderState :: forall a b. State -> Array (HH.HTML a b)
renderState End = [HH.div [] [ HH.text "End" ]]
renderState (Box s next) = [ renderStep s ] <> renderState next

renderStep :: forall a b. Step -> HH.HTML a b
renderStep step = HH.div [] [ HH.text "Step" ]

handleAction :: forall o m. Action -> H.HalogenM State Action () o m Unit
handleAction = case _ of
  Insert ->
    H.modify_ \st -> insertStep st (Action $ "action" :| [])