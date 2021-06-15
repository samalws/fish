import qualified Data.Set as S
import Data.Maybe
import Data.List

nonDup :: (Ord a) => [a] -> Bool
nonDup l = length l == length (S.fromList l)

allSame :: (Eq a) => [a] -> Bool
allSame [] = True
allSame (h:r) = all (== h) r

-- ord derivations are so they can be put into sets
data Card = Card { cardNum :: Int, cardSuit :: Int }              deriving (Show, Eq, Ord)
data Plr  = Plr  { plrNum :: Int }                                deriving (Show, Eq, Ord)
data Team = Team { teamNum :: Int }                               deriving (Show, Eq, Ord)
data Move = Move { moveCard :: Card, mover :: Plr, movee :: Plr } deriving (Show, Eq)
data Call = Call { callCards :: [(Plr, Card)],  caller :: Plr } deriving (Show, Eq)
data GameState = GameState { gamePlrs :: [(Plr, Team)], gameScores :: [(Team, Int)], gameHands :: [(Plr, [Card])], gameDran :: Plr } deriving (Eq, Show)

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
applyMove :: Move -> GameState -> GameState
applyMove m g = g { gameHands = newHands, gameDran = newDran } where
  cardFound = moveCard m `elem` plrHand (movee m) g
  newDran   = (if cardFound then mover else movee) m
  newHands  = (if cardFound then id else fmap f) $ gameHands g
  f (p, h)
    | p == mover m = (p, (:)    (moveCard m) h)
    | p == movee m = (p, delete (moveCard m) h)
    | otherwise    = (p, h)

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

main = return ()
