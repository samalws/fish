import qualified Data.Set as S
import Data.Maybe

nonDup :: (Ord a) => [a] -> Bool
nonDup l = length l == length (S.fromList l)

-- ord derivations are so they can be put into sets
data Card = Card { cardNum :: Int, cardSuit :: Int }              deriving (Show, Eq, Ord)
data Plr  = Plr  { plrNum :: Int }                                deriving (Show, Eq, Ord)
data Team = Team { teamNum :: Int }                               deriving (Show, Eq, Ord)
data Move = Move { moveCard :: Card, mover :: Plr, movee :: Plr } deriving (Show, Eq, Ord)
data GameState = GameState { gamePlrs :: [(Plr, Team)], gameScores :: [(Team, Int)], gameHands :: [(Plr, [Card])], gameDran :: Plr } deriving (Eq, Show)

fullDeck :: [Card]
fullDeck = [Card num suit | num <- [1..6], suit <- [1..9]]

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
validMove g m = goodCardSuit && goodCard && validCheckCard && moveeExists && goodMovee && moveeNonempty && goodMover where
  moverHand = plrHand (mover m) g
  goodCardSuit = cardSuit (moveCard m) `elem` fmap cardSuit moverHand
  goodCard = not $ elem (moveCard m) moverHand
  validCheckCard = validCard $ moveCard m
  moveeExists = elem (movee m) $ fst <$> gamePlrs g
  goodMovee = plrTeam (movee m) g /= plrTeam (mover m) g
  moveeNonempty = plrHand (movee m) g /= []
  goodMover = mover m == gameDran g

-- property that must hold: if validGameState g and validMove g m, then validGameState (applyMove m g)
applyMove :: Move -> GameState -> GameState
applyMove m g = g { gameHands = newHands, gameDran = newDran } where
  cardFound = elem (moveCard m) $ plrHand (movee m) g
  newDran = (if cardFound then mover else movee) m
  newHands = if cardFound then transferred else untransferred
  untransferred = gameHands g
  transferred   = f <$> gameHands g
  f (p, h)
    | p == mover m = (p, moveCard m : h)
    | p == movee m = (p, filter (/= moveCard m) h)
    | otherwise    = (p, h)

main = return ()
