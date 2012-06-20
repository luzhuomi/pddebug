

includes now ordering on environment

> {-# LANGUAGE GADTs, FlexibleInstances, BangPatterns #-} 

--------------------------------------------------------------------------------
-- Regular Expression Pattern Matching via Derivatives
--------------------------------------------------------------------------------

> module Main where

> import Monad
> import List 
> import Data.Bits
> import Char (ord)
> import GHC.IO
> import GHC.Int
> import qualified Data.IntMap as IM
> import qualified Data.ByteString.Char8 as S

> import System.IO.Unsafe

------------------------------
-- regular expressions

> data RE where
>   Phi :: RE                      -- empty language
>   Empty :: RE                    -- empty word
>   L :: Char -> Int -> RE                -- single letter with a position number
>   Choice :: RE  -> RE  -> RE     -- r1 + r2
>   Seq :: RE  -> RE  -> RE        -- (r1,r2)
>   Star :: RE  -> RE              -- r*
>  deriving Eq

A word is a byte string.

> type Word = S.ByteString

Pretty printing of regular expressions

> instance Show RE where
>     show Phi = "{}"
>     show Empty = "<>"
>     show (L c i) = show c ++ show i
>     show (Choice r1 r2) = ("(" ++ show r1 ++ "|" ++ show r2 ++ ")")
>     show (Seq r1 r2) = ("<" ++ show r1 ++ "," ++ show r2 ++ ">")
>     show (Star r) = (show r ++ "*")



annotate add position info to the regex

> newtype State s a = State { runState :: (s -> (a,s)) } 
 
> instance Monad (State s) where
>    -- return :: a -> State s a
>    return a        = State (\s -> (a,s))
>    -- (>>=) :: State s a -> (a -> State s b) -> State s b
>    (State x) >>= f = State (\s -> let (a,s') = x s 
>                                       stb = f a
>                                   in (runState stb) s')

> run :: s -> State s a -> (a,s)
> run s sta = (runState sta) s


> data CounterEnv = CounterEnv { cnt :: Int
>                              } deriving Show

> initEnv :: CounterEnv 
> initEnv = CounterEnv 0 

> nextCounter :: State CounterEnv Int
> nextCounter = State (\env -> let c = (cnt env) + 1
>                                  env' = c `seq` env{cnt=c}
>                              in env' `seq` (c, env'))


annotate a regex with position index

> rAnnotate :: RE -> RE
> rAnnotate r = case run initEnv (rAnn r) of
>              { (r', _ ) -> r' }  

> rAnn :: RE -> State CounterEnv RE
> rAnn Phi = return Phi
> rAnn Empty = return Empty
> rAnn (Choice r1 r2) = 
>   do { r1' <- rAnn r1
>      ; r2' <- rAnn r2
>      ; return (Choice r1' r2') }
> rAnn (Seq r1 r2) = 
>   do { r1' <- rAnn r1
>      ; r2' <- rAnn r2
>      ; return (Seq r1' r2') }
> rAnn (Star r) = 
>   do { r' <- rAnn r                
>      ; return (Star r') }
> rAnn (L c _) = 
>   do { i <- nextCounter       
>      ; return (L c i) }



> resToRE :: [RE] -> RE
> resToRE (r:res) = foldl Choice r res
> resToRE [] = Phi


> sigmaRE :: RE -> [Char]
> sigmaRE (L l _) = [l]
> sigmaRE (Seq r1 r2) = nub ((sigmaRE r1) ++ (sigmaRE r2))
> sigmaRE (Choice r1 r2) = nub ((sigmaRE r1) ++ (sigmaRE r2))
> sigmaRE (Star r) = sigmaRE r
> sigmaRE Phi = []
> sigmaRE Empty = []

> class IsEmpty a where
>     isEmpty :: a -> Bool

> instance IsEmpty RE where
>   isEmpty Phi = False
>   isEmpty Empty = True
>   isEmpty (Choice r1 r2) = (isEmpty r1) || (isEmpty r2)
>   isEmpty (Seq r1 r2) = (isEmpty r1) && (isEmpty r2)
>   isEmpty (Star r) = True
>   isEmpty (L _ _) = False

> type Loc = Int


> newtype DMonad h a = DMonad { runDM :: h -> (Maybe a, h) }

> instance Monad (DMonad s) where
>    return a = DMonad (\h -> (Just a,h) )
>    (DMonad x) >>= f = DMonad (\h -> let (mba, h') = x h 
>                                     in case mba of 
>                                        Just a -> runDM (f a) h'
>                                        Nothing -> (Nothing, h')) 

> instance MonadPlus (DMonad [Loc]) where
>    mzero = DMonad (\ls -> (Nothing, ls))
>    p `mplus` q = DMonad (\ls -> case runDM p ls of 
>              { (Nothing, _) -> runDM q ls 
>              ; (Just r, ls') -> (Just r, ls') })

> addLocM :: Loc -> DMonad [Loc] ()
> addLocM loc = DMonad (\h -> (Just (),h++[loc]))


> derivM :: RE -> Char -> DMonad [Loc] RE
> derivM Phi l = mzero
> derivM Empty l = mzero
> derivM (L l' loc) l | l == l' = addLocM loc >> return Empty
>                     | otherwise = mzero
> derivM (Seq r1 r2) l 
>  | isEmpty r1 = do 
>       { r1' <- derivM r1 l
>       ; return (Seq r1' r2)
>       } `mplus` derivM r2 l
>  | otherwise = do  
>       { r1' <- derivM r1 l
>       ; return (Seq r1' r2)
>       }
> derivM (Choice r1 r2) l = 
>  do { r1' <- derivM r1 l 
>     ; r2' <- derivM r2 l 
>     ; return (Choice r1' r2') } `mplus`  -- this is required otherwise we commit to d(r1) only
>  derivM r1 l `mplus` derivM r2 l

> derivM (Star r) l = do 
>  { r' <- derivM r l
>  ; return (Seq r' (Star r))
>  }


runDM  (do { r1' <- derivM  (rAnnotate r1) 'A' ; r1'' <- derivM r1' 'A' ; derivM r1'' 'A' }) []
           

a PDMonad is a State Monad / Parsec

s is the probably the history of the locations that a match visited
a is the resulting pd

> newtype PDMonad h a = PDMonad { runPDM :: h -> [(a,h)] } 
 
> instance Monad (PDMonad s) where
>    -- return :: a -> PDMonad s a
>    return a        = PDMonad (\h -> [(a,h)])
>    -- (>>=) :: PDMonad h a -> (a -> PDMonad h b) -> PDMonad h b
>    (PDMonad x) >>= f = PDMonad (\h -> {- nub2 $ -} concat [ runPDM (f a) h' | (a,h') <- x h ])


> instance MonadPlus (PDMonad [Loc]) where
>    mzero = PDMonad (\ls -> [])
>    p `mplus` q = PDMonad (\ls -> runPDM p ls ++ runPDM q ls)

                  

> nubM :: Eq r => PDMonad h r -> PDMonad h r
> nubM pdm = PDMonad (\h -> nub2 (runPDM pdm h))

> start = flip runPDM

> addLoc :: Loc -> PDMonad [Loc] ()
> addLoc loc = PDMonad (\h -> [((),h++[loc])])

> pderivM :: RE -> Char -> PDMonad [Loc] RE
> pderivM Phi l = mzero
> pderivM Empty l = mzero
> pderivM (L l' loc) l | l' == l = addLoc loc >> return Empty
>                      | otherwise = mzero
> pderivM (Choice r1 r2) l = nubM $ mplus (pderivM r1 l) (pderivM r2 l)
> pderivM (Star r) l = nubM $ do { r' <- pderivM r l 
>                         ; return (Seq r' (Star r))
>                         }
> pderivM (Seq r1 r2) l
>     | isEmpty r1 = nubM $ (do                                   
>        { r1' <- pderivM r1 l
>        ; return (Seq r1' r2) } `mplus` pderivM r2 l)
>     | otherwise = nubM $ do 
>        { r1' <- pderivM r1 l
>        ; return (Seq r1' r2) }
                  

start [] (do { r1' <- pderivM  (rAnnotate r1) 'A' ; r1'' <- nubM $ pderivM r1' 'A' ; pderivM r1'' 'A' })

> nub2 :: Eq a => [(a,b)] -> [(a,b)]
> nub2 = nubBy (\(p1,f1) (p2, f2) -> p1 == p2) 





> r = rAnnotate (Choice (Star (Seq (L 'A' 0) (L 'B' 0))) (L 'B' 0))   -- ((A,B)*|B)


> r1 = rAnnotate (Seq (Star (L 'A' 0)) (Star (L 'A' 0)))


> r2 = rAnnotate (Choice (Seq (L 'A' 0) (L 'A' 0)) (Seq (L 'A' 0) (L 'B' 0)))
