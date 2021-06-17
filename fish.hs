import qualified Data.Set as S
import Control.Applicative
import Data.Maybe
import Data.List

nonDup :: (Ord a) => [a] -> Bool
nonDup l = length l == length (S.fromList l)

allSame :: (Eq a) => [a] -> Bool
allSame [] = True
allSame (h:r) = all (== h) r

modifySnd :: (a -> b -> b) -> (a, b) -> (a, b)
modifySnd f (x,y) = (x, f x y)

-- rotate l until x is first
rotateMakingFirst :: (Eq a) => a -> [a] -> [a]
rotateMakingFirst x l
  | x `elem` l = helper l
  | otherwise  = l -- error condition: x is not in l, so we don't rotate
  where
    helper [] = []
    helper (h:r)
      | h == x = (h:r)
      | otherwise = helper (r ++ [h])

-- Ord derivations are so they can be put into sets
data Card = Card { cardNum :: Int, cardSuit :: Int }              deriving (Show, Eq, Ord)
data Plr  = Plr  { plrNum :: Int }                                deriving (Show, Eq, Ord)
data Team = Team { teamNum :: Int }                               deriving (Show, Eq, Ord)
data Move = Move { moveCard :: Card, mover :: Plr, movee :: Plr } deriving (Show, Eq)
data Call = Call { callCards :: [(Plr, Card)],  caller :: Plr } deriving (Show, Eq)
data GameState = GameState { gamePlrs :: [(Plr, Team)], gameScores :: [(Team, Int)], gameHands :: [(Plr, [Card])], gameDran :: Plr } deriving (Eq, Show)
-- dran is German, sorta meaning "whose turn": "du bist dran" = "you are dran" = "it's your turn"
-- I used it because there's no good English equivalent

numCardNums :: Int
numCardNums = 6

numCardSuits :: Int
numCardSuits = 9

fullDeck :: [Card]
fullDeck = [Card num suit | num <- [1..numCardNums], suit <- [1..numCardSuits]]

fullDeckSet :: S.Set Card
fullDeckSet = S.fromAscList fullDeck

validCard :: Card -> Bool
validCard = flip S.member fullDeckSet

validGameState :: GameState -> Bool
validGameState g = matchingPlrs && matchingTeams && validHands && validDran && nonDupPlrs && nonDupHandPlrs && nonDupScores && nonDupHands where

  plrList1  = fst <$> gamePlrs   g
  plrList2  = fst <$> gameHands  g
  teamList1 = snd <$> gamePlrs   g
  teamList2 = fst <$> gameScores g
  cardList  = concat $ snd <$> gameHands g

  matchingPlrs  = S.fromList plrList1  == S.fromList plrList2
  matchingTeams = S.fromList teamList1 == S.fromList teamList2

  validHands = all validCard cardList
  validDran  = gameDran g `elem` plrList1

  nonDupPlrs     = nonDup plrList1
  nonDupHandPlrs = nonDup plrList2
  nonDupScores   = nonDup teamList2
  nonDupHands    = nonDup cardList

plrHand :: Plr -> GameState -> [Card]
plrHand p = fromMaybe [] . lookup p . gameHands

plrTeam :: Plr -> GameState -> Maybe Team
plrTeam p = lookup p . gamePlrs

validMove :: GameState -> Move -> Bool
validMove g m = validCheckCard && cardSuitInHand && cardNotInHand && moveeExists && moveeRightTeam && moveeNonempty && moverDran where
  card      = moveCard m
  mvee      = movee    m
  mver      = mover    m
  moverHand = plrHand mver g

  validCheckCard = validCard card
  cardSuitInHand = cardSuit card `elem` (cardSuit <$> moverHand)
  cardNotInHand  = not $ card `elem` moverHand
  moveeExists    = mvee `elem` (fst <$> gamePlrs g)
  moveeRightTeam = plrTeam mvee g /= plrTeam mver g
  moveeNonempty  = plrHand mvee g /= []
  moverDran      = mver == gameDran g

-- property that must hold: if validGameState g and validMove g m, then validGameState (applyMove m g)
-- applyMove m g is undefined if not (validGameState g and validMove g m)
applyMove :: Move -> GameState -> GameState
applyMove m g = g { gameHands = newHands, gameDran = newDran } where
  cardFound = moveCard m `elem` plrHand (movee m) g
  newDran   = (if cardFound then mover else movee) m
  newHands  = (if cardFound then id else modifySnd f) <$> gameHands g
  f plr
    | plr == mover m = (:)    (moveCard m)
    | plr == movee m = delete (moveCard m)
    | otherwise      = id

validCall :: GameState -> Call -> Bool
validCall g c = goodCaller && goodPlrs && goodCards && rightNumCards && nonDupPlrs && nonDupCards where
  clr   = caller c
  crds  = callCards c
  plrs  = fst <$> crds
  cards = snd <$> crds

  goodCaller    = clr `elem` (fst <$> gamePlrs g)
  goodPlrs      = all (\p -> plrTeam p g == plrTeam clr g) plrs
  goodCards     = all validCard cards && allSame (cardSuit <$> cards)
  rightNumCards = length cards == numCardSuits

  nonDupPlrs  = nonDup plrs
  nonDupCards = nonDup cards

-- property that must hold: if validGameState g and validCall g c, then validGameState (applyCall c g)
-- applyCall c g is undefined if not (validGameState g and validCall g c)
applyCall :: Call -> GameState -> GameState
applyCall c g = g { gameScores = newScores, gameHands = newHands, gameDran = newDran } where

  -- add or subtract 1 from the caller's team's score
  newScores   = modifySnd f <$> gameScores g

  -- remove cards of the called suit from all hands
  newHands    = (h <$>) <$> gameHands g

  -- look for the first player whose hand isn't empty, starting at current dran, and then continuing rightward along the player list
  newDran     = fromMaybe (gameDran g) $ i $ rotateMakingFirst (gameDran g) $ fst <$> gamePlrs g

  correctCall = all j $ callCards c

  scoreToAdd  = if correctCall then 1 else -1
  callTeam    = plrTeam (caller c) g
  callSuit    = listToMaybe $ (cardSuit . snd) <$> callCards c

  f team
    | callTeam == pure team = (+) scoreToAdd
    | otherwise             = id

  h = filter $ (/= callSuit) . pure . cardSuit

  i (plr:r)
    | lookup plr newHands /= pure [] = pure plr
    | otherwise                      = i r
  i [] = empty

  j (plr, card) = card `elem` plrHand plr g

-- game is finished if everyone's hands are empty
gameIsFinished :: GameState -> Bool
gameIsFinished = (== []) . mconcat . (snd <$>) . gameHands

-- the one with the highest score
gameWinner :: GameState -> Maybe Team
gameWinner = snd . foldr f (Nothing, Nothing) . gameScores where
  f (t, s) (Nothing, _) = (Just s, Just t)
  f (t, s) (Just ss, tt)
    | s > ss    = (Just  s, Just t)
    | s < ss    = (Just ss, tt)
    | otherwise = (Just ss, Nothing)

main = return ()
