{-# LANGUAGE TupleSections #-}

import qualified Data.Set as S
import Control.Applicative
import Data.Maybe
import Data.List
import System.Random
import Control.Concurrent

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
data ListenIOResponse = RequestPlrs | RequestScores | RequestHand | RequestDran | SubmitMove Move | SubmitCall Call
data GameIO s = GameIO { startIO         ::                              IO ([(Plr, Team)], Plr, s),
                         listenIO        :: s                         -> IO (Plr, ListenIOResponse),
                         alertPlrsIO     :: s -> Plr -> [(Plr, Team)] -> IO (),
                         alertScoresIO   :: s -> Plr -> [(Team, Int)] -> IO (),
                         alertHandIO     :: s -> Plr -> [Card]        -> IO (),
                         alertDranIO     :: s -> Plr -> Plr           -> IO (),
                         alertGameOverIO :: s -> Plr                  -> IO (),
                         alertMoveIO     :: s -> Move -> Bool         -> IO (),
                         alertCallIO     :: s -> Call -> Bool         -> IO ()
                       }

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

moveWorks :: Move -> GameState -> Bool
moveWorks m g = moveCard m `elem` plrHand (movee m) g

-- property that must hold: if validGameState g and validMove g m, then validGameState (applyMove m g)
-- applyMove m g is undefined if not (validGameState g and validMove g m)
applyMove :: Move -> GameState -> GameState
applyMove m g = g { gameHands = newHands, gameDran = newDran } where
  cardFound = moveWorks m g
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

callWorks :: Call -> GameState -> Bool
callWorks c g = all f $ callCards c where
  f (plr, card) = card `elem` plrHand plr g

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

  correctCall = callWorks c g
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

shuffleDeck :: (RandomGen g) => [Card] -> g -> ([Card], g)
shuffleDeck [] rng = ([], rng)
shuffleDeck d  rng = (newD, rng3) where
  (chosenNum, rng2) = randomR (0, length d - 1) rng
  chosenElem = d !! chosenNum
  elemRemoved = take (chosenNum - 1) d ++ drop chosenNum d
  (restShuffled, rng3) = shuffleDeck elemRemoved rng2
  newD = chosenElem : restShuffled

makeNHands :: [Card] -> Int -> [[Card]]
makeNHands _ 0 = []
makeNHands d 1 = [d]
makeNHands d n = take m d : makeNHands (drop m d) (n-1) where m = length d `div` n

makeNRandomHands :: (RandomGen g) => [Card] -> Int -> g -> ([[Card]], g)
makeNRandomHands d n rng = (makeNHands d2 n, rng2) where (d2, rng2) = shuffleDeck d rng

dealNPlayers :: (RandomGen g) => Int -> g -> ([[Card]], g)
dealNPlayers = makeNRandomHands fullDeck

-- property that must hold: if (fst <$> plrs) contains no duplicates and (dran `elem` plrs), then validGameState (fst (makeGame plrs dran rng))
makeGame :: (RandomGen g) => [(Plr, Team)] -> Plr -> g -> (GameState, g)
makeGame plrs dran rng = (GameState { gamePlrs = plrs, gameScores = scores, gameHands = hands, gameDran = dran }, rng2) where
  teamList = S.toList $ S.fromList $ snd <$> plrs
  scores = (, 0) <$> teamList
  (handList, rng2) = dealNPlayers (length plrs) rng
  hands = zip (fst <$> plrs) handList

respondToListen :: GameIO s -> s -> GameState -> Plr -> ListenIOResponse -> IO GameState
respondToListen gio s game plr RequestPlrs   = (alertPlrsIO   gio s plr $ gamePlrs    game) >> pure game
respondToListen gio s game plr RequestScores = (alertScoresIO gio s plr $ gameScores  game) >> pure game
respondToListen gio s game plr RequestHand   = (alertHandIO   gio s plr $ plrHand plr game) >> pure game
respondToListen gio s game plr RequestDran   = (alertDranIO   gio s plr $ gameDran    game) >> pure game
respondToListen gio s game plr (SubmitMove move)
  | not (validMove game move) = pure game
  | otherwise = do
      let newGame = applyMove move game
      let worked  = moveWorks move game
      alertMoveIO gio s move worked
      pure newGame
respondToListen gio s game plr (SubmitCall call)
  | not (validCall game call) = pure game
  | otherwise = do
      let newGame = applyCall call game
      let worked  = callWorks call game
      alertCallIO gio s call worked
      pure newGame

runIngameIOLoop :: GameIO s -> s -> GameState -> IO ()
runIngameIOLoop gio s game
  | gameIsFinished game = gameFinishedIO gio s game
  | otherwise = do
      (plr, response) <- listenIO gio s
      newGame         <- respondToListen gio s game plr response
      runIngameIOLoop gio s newGame

gameFinishedIO :: GameIO s -> s -> GameState -> IO ()
gameFinishedIO gio s game = pure () -- TODO

runIngameIO :: GameIO s -> ([(Plr, Team)], Plr, s) -> IO ()
runIngameIO gio (plrs, dran, s) = do
  game <- getStdRandom $ makeGame plrs dran
  runIngameIOLoop gio s game

runFullGameIO :: GameIO s -> IO ()
runFullGameIO gio = do
  info <- startIO gio
  forkIO $ runIngameIO gio info
  runFullGameIO gio

main = return ()
