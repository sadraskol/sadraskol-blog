module Style where

import CSS

import CSS.Common (class None, auto, center, none)
import CSS.ListStyle.Type (listStyleType)
import CSS.Overflow (hidden, overflow)
import Data.Maybe (fromJust)
import Data.NonEmpty (singleton)
import Partial.Unsafe (unsafePartial)
import Prelude (discard, ($))

data Cursor = Cursor Value
instance valCursor :: Val Cursor where
  value (Cursor v) = v

cursor :: Cursor -> CSS
cursor = key $ fromString "cursor"

pointer :: Cursor
pointer = Cursor $ fromString "pointer"

data OverflowWrap = OverflowWrap Value

instance valOverflowWrap :: Val OverflowWrap where
  value (OverflowWrap v) = v

overflowWrap :: OverflowWrap -> CSS
overflowWrap = key $ fromString "overflow-wrap"

breakWord :: OverflowWrap
breakWord = OverflowWrap $ fromString "break-word"

data Resize = Resize Value

instance valResize :: Val Resize where
  value (Resize v) = v

instance noneResize :: None Resize where
  none = Resize $ fromString "none"

resize :: Resize -> CSS
resize = key $ fromString "resize"

defaultList :: CSS
defaultList = do
  padding nil nil nil nil
  margin nil nil nil nil
  listStyleType none

sadraskolStyle :: Rendered
sadraskolStyle = render do
  ul ? defaultList
  ol ? defaultList
  a ? do
    color linksColor
    textDecoration noneTextDecoration
  fromString "a:hover" ? do
    textDecoration underline
    cursor pointer
  fromString "a:visited" ? do
    color secondaryColor
  body ? do
    margin nil nil nil nil
    fontFamily ["Helvetica Neue", "Helvetica", "Arial"] (singleton sansSerif)
    backgroundColor backgroudColor
    color paragraphColor

  strong ? color headlineColor

  fromString "header" ? do
    display flex
    flexDirection row
    justifyContent spaceBetween 
    color headlineColor

    ul ? alignSelf center
    fromString "nav" ? do
      paddingTop $ em 1.0
      paddingBottom $ em 1.0

  fromString ".container" ? do
    width $ px 900.0
    margin nil auto nil auto

  fromString ".overview-menu__item" ? do
    display inlineBlock
    padding (px 15.0) (px 30.0) (px 15.0) nil

  fromString ".draft-item" ? do
    margin (em 1.0) nil nil nil
  fromString ".draft-item:last-child" ? do
    marginBottom (em 1.0)
  fromString ".draft-item__actions" ? do
    padding (px 3.0) nil nil nil
  fromString ".draft-item__actions__item" ? do
    display inlineBlock
    padding nil (px 30.0) nil nil

  fromString ".post-item" ? do
    margin (em 1.0) nil nil nil
  fromString ".post-item:last-child" ? do
    marginBottom (em 1.0)
  fromString ".post-item__actions" ? do
    padding (px 3.0) nil nil nil
  fromString ".post-item__actions__item" ? do
    display inlineBlock
    padding nil (px 30.0) nil nil

  fromString ".editor-header" ? do
    width $ px 900.0
    margin nil auto nil auto
    height $ px 46.0
    zIndex 20
    backgroundColor white
    display flex
    alignItems center
    padding nil nil nil nil
    position fixed
    top $ px 158.0
    left nil
    right nil
    a ? do marginRight $ px 10.0
  fromString ".editor-header__right" ? do
    display flex
    marginLeft auto
  fromString ".editor-language__select" ? do
    backgroundColor $ hsla 0.0 0.0 0.0 0.0
    overflow hidden
    border solid nil black
    borderRadius nil nil nil nil
    boxSizing borderBox
    padding (px 6.0) (px 16.0) (px 6.0) (px 16.0)

  fromString ".editor" ? do
    paddingTop $ px 46.0

  fromString ".editor-title" ? do
    width $ px 700.0
    margin nil auto nil auto
  fromString ".editor-title__input" ? do
    overflow hidden
    border solid nil black
    borderBottom solid (px 1.0) black
    borderRadius nil nil nil nil
    boxSizing borderBox
    width $ pct 100.0
    height $ pct 100.0
    padding (px 6.0) (px 16.0) (px 6.0) (px 16.0)
    marginBottom (em 1.0)

  fromString ".editor-content" ? do
    width $ px 700.0
    margin nil auto nil auto
  fromString ".editor-content__textarea" ? do
    resize none
    border solid nil black
    borderRadius nil nil nil nil
    boxSizing borderBox
    width $ pct 100.0
    padding (px 6.0) (px 16.0) (px 6.0) (px 16.0)

-- https://happyhues.co
backgroudColor :: Color
backgroudColor = unsafePartial $ fromJust $ fromHexString "#faeee7"
headlineColor :: Color
headlineColor = unsafePartial $ fromJust $ fromHexString "#33272a"
paragraphColor :: Color
paragraphColor = unsafePartial $ fromJust $ fromHexString "#594a4e"
buttonColor :: Color
buttonColor = unsafePartial $ fromJust $ fromHexString "#ff8ba7"
buttonTextColor :: Color
buttonTextColor = unsafePartial $ fromJust $ fromHexString "#33272a"
strokeColor :: Color
strokeColor = unsafePartial $ fromJust $ fromHexString "#33272a"
mainColor :: Color
mainColor = unsafePartial $ fromJust $ fromHexString "#fffffe"
highlightColor :: Color
highlightColor = unsafePartial $ fromJust $ fromHexString "#ff8ba7"
secondaryColor :: Color
secondaryColor = unsafePartial $ fromJust $ fromHexString "#ffc6c7"
tertiaryColor :: Color
tertiaryColor = unsafePartial $ fromJust $ fromHexString "#c3f0ca"
linksColor :: Color
linksColor = unsafePartial $ fromJust $ fromHexString "#ff8ba7"