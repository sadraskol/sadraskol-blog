module Sadraskol.Types where

import Sadraskol.Api

data Action
  = Init
  | GoToPosts
  | GoToDrafts
  | MakePublic BlogDraft
  | GoEditDraft BlogDraft
  | CloseDraftEditing
  | EditNewDraft BlogDraft
  | UpdateDraftContent String
  | UpdateDraftTitle String
  | UpdateDraftLanguage Language