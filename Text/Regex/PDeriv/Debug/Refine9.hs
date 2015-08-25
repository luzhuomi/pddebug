{-# LANGUAGE GADTs, UnboxedTuples #-}



{-
based Refine8, turning ROp into integer representation


data ROp = RATr Re RLevel  -- add transition
         | RASt Re RLevel  -- add state
         | RMkFin RLevel    -- make final
         | RNoCh RLevel     -- no change
          deriving (Show)


since Re is label actually, hence 

we use integer with 4 digits

1st digit  from the most significant pos : 
    0 -> RAtr Strong,
    1 -> RAtr Weak,
    2 -> RASt Strong,
    3 -> RAst Weak,
    4 -> RMkFin Strong, 
    5 -> RMKFin Weak,
    6 -> RNoCh Strong
    7 -> RNoCh Weak
2nd,3rd and 4digit, the label in ascii code 




Based on Refine6, optimized,

The regular expression refinement algorithm

Inspired by the type checking system and type inference algorithm found in programming language research communities. \cite{TODO}

Type checking and Type inference algorithm
==========================================

Type checking judgement
-----------------------

$\gamma \vdash e : t$ 
Given the type environemnt $\gamma$, the program expression e and the type $t$, the above is deducable if $e$ has type $t$ under the type environment $\gamma$

Note that the type checking is a relation, where $\gamma$, $e$ and $t$ are the inputs.

Type inference judgement
------------------------

$\gamma \models e : t$

Given the type environment \gamma and the program expression e the algorithm reconstructs the type t.

Note that the type inference is considered an function, where \gamma and e are the inputs.

 * Type inference correctness 

$\gamma \models e : t$ 
implies 
$\gamma \vdash e : t$ 




Regular expression debugging and refinement
===============================================

The connection
--------------


Pointed out the XDuce work, we consider the correspondence between the program expression $e$ and the document $d$,
the type $t$ and the regular expression $r$.

 * The word problem  $d \in r$ corresponds to the type checking problem.

The difference
--------------

 * The matching problem 

 $$ d \in r \Longrightarrow \Delta $$ 

where r is annotated with a label at each AST level. $\Delta$ maps labels to sub-matches.


The mechanism
-------------

We use partial derivative operations to implement the word problem and the sub matching problem. See our recent papers (PPDP 12 )


The debugging algorithm
-----------------------

Refer to the PDDebug.lhs

The Refinement checking judgement
---------------------------------


-}


module Text.Regex.PDeriv.Debug.Refine9 where

import System.Environment 
import qualified Data.Map as M
import qualified Data.IntMap as IM
import System.IO.Unsafe
import Data.List 
import Data.Maybe
import Data.Char
import qualified Data.IntSet as Set

import Control.Monad.ST
import Data.STRef
import Control.Monad
 
import Control.Monad.State
  
import Text.Regex.PDeriv.Parse
-- import qualified Text.Regex.PDeriv.RE as R
-- import Text.Regex.PDeriv.IntPattern
import Text.Regex.PDeriv.ExtPattern



import qualified Data.ByteString.Char8 as S


logger mesg = unsafePerformIO $ print mesg

{-
 * The problem

Let  $\gamma$ denote the user specification, $w$ denote the input word , $r$ the pattern and  $r'$ the refined pattern, 
we use the judgement 
$$\gamma, r \vdash d : r'$$ 
to denote that under the user spec $\gamma$ , $r'$ is a replacement of $r$ that accepts $w$.

 * The user requirement 

\gamma ::= { (i, r) , ... , }
i ::= 1,2,3,...

-} 

type SrcLoc = Int

-- ^ The user requirement is a mapping of labels to the regexs 

type UReq = [(Int, Re)]

lookupUR :: Int -> UReq -> Maybe Re
lookupUR i env = lookup i env

updateUR :: Int -> Re -> UReq -> UReq
updateUR x r ureq = map (\(y,t) -> if (x == y) then (y,r) else (y,t)) ureq

allAccEps :: UReq -> Bool
allAccEps ureq = all (\(x,t) -> posEmpty t) ureq

inUR :: Int -> UReq -> Bool
inUR i env = isJust (lookupUR i env) 

{- * The Regular expression 
             
p ::= r^i 
r ::= () || (p|p) || pp || p* || l || \phi 
-}
                          
data Re where
  Choice :: SrcLoc -> [Re] -> Re
  Pair :: SrcLoc -> Re -> Re -> Re
  Star :: SrcLoc -> Re -> Re
  Ch :: SrcLoc -> Char -> Re
  Eps :: SrcLoc -> Re
  Phi :: Re
  Any :: SrcLoc -> Re
 deriving (Show)


instance Ord Re where
  compare Phi Phi = EQ
  compare Phi _ = LT
  compare _ Phi = GT
  compare (Eps _) (Eps _) = EQ
  compare (Eps _) _ = LT
  compare _ (Eps _) = GT
  compare (Any _) (Any _) = EQ
  compare (Any _) _ = LT
  compare _ (Any _) = GT
  compare (Ch _ x) (Ch _ y) = compare x y
  compare (Ch _ _) _ = LT
  compare _ (Ch _ _) = GT
  compare (Pair _ r1 r2) (Pair _ r3 r4) = case compare r1 r3 of
    { EQ -> compare r2 r4
    ; otherwise -> otherwise 
    }
  compare (Pair _ _ _) _ = LT
  compare _ (Pair _ _ _) = GT
  compare (Choice _ rs) (Choice _ rs') = compare rs rs'
  compare (Choice _ _) _ = LT
  compare _ (Choice _ _) = GT
  compare (Star _ r) (Star _ r') = compare r r'

  

instance Eq Re where
  (==) (Choice _ rs1) (Choice _ rs2) = rs1 == rs2
  (==) (Pair _ r1 r2) (Pair _ r1' r2') = r1 == r1' && r2 == r2'
  (==) (Star _ r1) (Star _ r2) = r1 == r2
  (==) (Ch _ c1) (Ch _ c2) = c1 == c2
  (==) Eps{} Eps{} = True
  (==) Phi Phi = True
  (==) (Any _) (Any _) = True
  (==) _ _ = False

pretty :: Re -> String
pretty (Choice _ rs) = "(" ++ interleave "|" (map pretty rs) ++ ")"
pretty (Pair _ r1 r2) = "(" ++ pretty r1 ++ "," ++ pretty r2 ++ ")"
pretty (Star _ r1) = pretty r1 ++ "*"
pretty (Ch _ c1) = [c1]
pretty (Eps _) = "()"
pretty (Any _) = "."
pretty Phi = "{}"

interleave :: String -> [String] -> String
interleave _ [] = ""
interleave _ [x] = x
interleave d (x:xs) = x ++ d ++ interleave d xs

posEmpty :: Re -> Bool
posEmpty (Eps _)        = True
posEmpty (Choice _ rs)  = any posEmpty rs
posEmpty (Pair _ r1 r2) = posEmpty r1 && posEmpty r2
posEmpty (Star _ _)     = True
posEmpty (Ch _ _)       = False
posEmpty (Any _)        = False
posEmpty Phi            = False

isPhi :: Re -> Bool 
isPhi Phi            = True
isPhi (Ch _ _ )      = False
isPhi (Choice _ rs)  = all isPhi rs
isPhi (Pair _ r1 r2) = isPhi r1 || isPhi r2 
isPhi (Star _ _)     = False
isPhi (Eps _)        = False
isPhi (Any _)        = False

isChoice :: Re -> Bool
isChoice Choice{} = True
isChoice _ = False


-- containment check

contain :: Re -> Re -> Bool
contain r1 r2 = containBy M.empty r2 r1

data Leq = Leq Re Re deriving (Eq, Ord, Show)

containBy :: M.Map Leq () -> Re -> Re -> Bool
containBy env Phi _ = True
containBy env r1 r2 = 
  case M.lookup (Leq r1 r2) env of   
   { Just _  -> True  
   ; Nothing | posEmpty r1 && not (posEmpty r2) -> False
             | otherwise -> let env' = M.insert (Leq r1 r2)  () env
                            in  all (\l -> containBy env' (deriv r1 l) (deriv r2 l)) (sigma (Choice dontcare [r1,r2]))
   }
deriv r l = Choice dontcare (pderiv r l)

-- semantic equivalence check

equiv :: Re -> Re -> Bool
equiv r1 r2 = r1 `contain` r2 && r2 `contain` r1


-- the simplification 
{-
collapse x y = nub (sort (x ++ y))
combine x y = nub (sort (x ++ y))

shift :: [Int] -> Re -> Re 
shift ls Phi = Phi
shift ls (Choice ls' rs) = Choice (combine ls' ls) rs
shift ls (Ch ls' c) = Ch (combine ls' ls) c
shift ls (Pair ls' r1 r2) = Pair (combine ls' ls) r1 r2
shift ls (Star ls' r) = Star (combine ls' ls) r
shift ls (Eps ls') = Eps (combine ls' ls)
shift ls (Any ls') = Any (combine ls' ls)
-}

simpl :: Re -> REnv -> (Re, REnv)
simpl (Pair l1 (Eps l2) r) renv 
  | isPhi r  = (Phi,renv)
  | otherwise = (r,renv) -- todo:check
simpl (Pair l r1 r2) renv 
  | isPhi r1 || isPhi r2 = (Phi,renv)
  | otherwise            = let (r1', renv') = simpl r1 renv
                               (r2', renv'') = simpl r2 renv'                               
                           in (Pair l r1' r2', renv'')
simpl (Choice l []) renv = (Eps l, renv)
simpl (Choice l [r]) renv = case getLabel r of 
  { (l':_) -> (r,  reloc l l' renv) -- todo: check
  ; _ -> (r, renv) -- r is phi
  }
simpl (Choice l rs) renv 
  | any isChoice rs = 
     let (rs',e') = foldl (\(rs,e) -> \r -> case r of
                    { Choice l' rs2 -> ((rs ++ (map {- (shift l')-} id  rs2)), reloc l' l e)
                    ; _             -> (rs ++ [r], e) }) ([],renv) rs 
     in (Choice l rs', e')
  | otherwise = 
       let (rs',e'') = foldl (\(rs,e) -> \r-> 
                               let (r',e') = simpl r e                 
                               in if isPhi r'
                                  then (rs,e')
                                  else (rs++[r],e')                                   
                             ) ([],renv) rs -- todo: check for duplicate
       in (Choice l rs', e'')
simpl (Star l1 (Eps l2)) renv = (Eps l2, reloc l1 l2 renv) --todo:
simpl (Star l1 (Star l2 r)) renv = (Star l2 r, reloc l1 l2 renv)
simpl (Star l r) renv
  | isPhi r   = (Eps l, renv)
  | otherwise = let (r',e) = simpl r renv in (Star l r',e)
simpl x e = (x,e)

-- simplication w/o changing the REnv
{-
simp :: Re -> Re
simp (Pair l1 (Eps l2) r) 
  | isPhi r   = Phi
  | otherwise = shift (collapse l1 l2) r
simp (Pair l r1 r2)
  | isPhi r1 || isPhi r2 = Phi
  | otherwise            = Pair l (simp r1) (simp r2)
simp (Choice l []) = Eps l
simp (Choice l [r]) = shift l r
simp (Choice l rs) = Choice l $ nub $ filter (not.isPhi) $ map simp rs
simp (Star l1 (Eps l2)) = Eps $ collapse l1 l2 
simp (Star l1 (Star l2 r)) = Star (combine l1 l2) r 
simp (Star l r)
  | isPhi r   = Eps l
  | otherwise = Star l $ simp r 
simp x = x 
-}




class PDeriv t where
  pderiv :: t -> Char -> [Re]

-- partial derivatives of regex

instance PDeriv Re where
  pderiv (Eps _) _ = []
  pderiv (Choice x rs) l = 
    nub (concatMap (\r -> pderiv r l) rs )
  pderiv (Pair x r1 r2) l | posEmpty r1 = nub [ Pair x r1' r2 | r1' <- pderiv r1 l] ++ (pderiv r2 l)
                          | otherwise =  [ Pair x r1' r2 | r1' <- pderiv r1 l]
  pderiv (Star x r) l = [ Pair x r' (Star x r) | r' <- pderiv r l ]
  pderiv (Ch x c) l | c == l = [ Eps x ]
                    | otherwise = []
  pderiv (Any x) l = [ Eps x ]
  pderiv Phi _ = []

  


-- * partial derivatives of a set of regexs

instance PDeriv t => PDeriv [t] where
  pderiv rs l = concatMap (\r -> pderiv r l) rs

-- * partial dervatives extended to user-requirement-regex pair

{- 
We need to annotate the URPair with the recommendation info to 'disambiguate' the refinement process. 
To elaborate, we first need to consider the extension of partial derivative operation over the user-requirement-regex pairs.

 ** Case: i \not\in dom(\gamma)
                    
  (\gamma, \epsilon_i) / l = {}                 -- (Eps1) 
  (\gamma, l_i) / l = { (\gamma, \epsilon_i) }  -- (LabMatch1)
  (\gamma, l_i') / l = { }                      -- (LabMisMatch1)                   
  (\gamma, (r1r2)_i) /l | \epsilon \in r1 = { (\gamma' ++ \gamma(fv(r2)), (r1'r2)_i) | (\gamma', r1') <- (\gamma(fv(r1)), r1) / l } ++  (\gamma(fv(r2)), r2) / l
                        | otherwise  = { (\gamma' ++ \gamma(fv(r2)), (r1'r2)_i) | (\gamma', r1') <- (\gamma(fv(r1)), r1) / l }   
                                                -- (Pair1) 
  (\gamma, (r1|r2)_i) / l = (\gamma(fv(r1_i)), r1_i)/l ++ (\gamma(fv(r2_i)), r2_i)/l   -- (Choice1)
  (\gamma, r*_i) / l = { (\gamma', (r'r*)_i) | (\gamma', r') <- (\gamma, r) / l }      -- (Star1)
                    
 ** Case: i \in dom(\gamma)
  (\gamma, \epsilon_i) / l = {}                 -- (Eps2) 
  (\gamma, l_i) / l = { (\gamma,\epsilon_i) }   -- (LabMatch2)
  (\gamma, l_i') / l = { }                      -- (LabMisMatch2)                   
  (\gamma, (r1r2)_i) /l | \epsilon \in r1 = { (\gamma' ++ \gamma(fv(r2)) ++ { (i, \gamma(i)/l) } , (r1'r2)_i) | (\gamma', r1') <- (\gamma(fv(r1)), r1) / l } ++  (\gamma(fv(r2)), r2) / l
                        | otherwise  = { (\gamma' ++ \gamma(fv(r2)), (r1'r2)_i) | (\gamma', r1') <- (\gamma(fv(r1)), r1) / l }
                                                -- (Pair2)
  (\gamma, (r1|r2)_i) /l = (\gamma(fv(r1_i)), r1_i)/l ++ (\gamma(fv(r2_i)), r2_i) /l  -- (Choice2)
  (\gamma, r*_i) / l = { (\gamma', (r'r*)_i) | (\gamma', r') <- (\gamma, r) / l }     -- (Star2)
                    
                    
                  
NOTE: \gamma([i1,...,in]) denotes { (i,r) | (i,r) \in \gamma, i \in { i1,..., in } }                  
               
  The above formulation does not refine in case of failure, i.e. pd yields { }. See cases (Eps1), (Eps2), (LabMistMach1) and (LabMistMach2).
                  

e.g. given p = x :: (a|b)*  and w = c, matching w with p using partial derivative operation
 
                  p / c = {} 
                  
                  whichis a matching failure
                  
 This is because p / c -->                   
                 { (r, p) | r <- (a|b) /c }
     and                  
                 (a|c) / c -->
                 a/c U b/c -->
                  {} U {}  --> 
                     {}
                  
Suppose the user requirement enforces that x should match with a non-empty word e.g. { x :: .+ }, note that '.' matches with any single symbol.

One naive way to refine the pattern p is to just update by replacing (a|b)* with .+, however doing so is often too liberal, because the user requirement could be specified loosely.

An immediate (less naive) fix would be adjusting the partial derivative operations as follows,


 We adjust the pd operation to return the refinement environment besides the partial derivatives

 ** Case: i \not\in dom(\gamma)
                    
  (\gamma, \epsilon_i) /^{level} l = { (\gamma, \epsilon_j, {i : seq+ l_j (max level weak)}) }                   -- (Eps1') 
  (\gamma, l_i) /^{level} l        = { (\gamma, \epsilon_i, {}) }                                    -- (LabMatch1)
  (\gamma, l'_i) /^{level} l       = { (\gamma, \epsilon_i, {i : choice+ l_j (max level weak)}) }                -- (LabMisMatch1')                   
  (\gamma, (r1r2)_i) /^{level}l | \epsilon \in r1 = { (\gamma' ++ \gamma(fv(r2)), (r1'r2)_i, \theta) | (\gamma', r1', \theta) <- (\gamma(fv(r1)), r1) /^{level} l } ++  (\gamma(fv(r2)), r2) /^{level} l
                                | otherwise       = { (\gamma' ++ \gamma(fv(r2)), (r1'r2)_i, \theta) | (\gamma', r1'. \theta) <- (\gamma(fv(r1)), r1) /^{level} l }  
                                                                                             -- (Pair1)                                               
  (\gamma, (r1|r2)_i) /^{level} l = (\gamma(fv(r1_i)), r1_i)/^{level}l ++ (\gamma(fv(r2_i)), r2_i)/^{level}l           -- (Choice1)
  (\gamma, r*_i) /^{level} l = { (\gamma', (r'r*)_i) | (\gamma', r', \theta) <- (\gamma, r) /^{level} l }    -- (Star1)
                    
 ** Case: i \in dom(\gamma)
  (\gamma, \epsilon_i) /^{level} l = { (\gamma', \epsilon_j, {i : seq+ l_j strong}) | \gamma' <- \gamma / l }   -- (Eps2') 
  (\gamma, l_i) /^{level} l        = { (\gamma,  \epsilon_i, {}) }                                              -- (LabMatch2)             
  (\gamma, l_i') /^{level} l       = { (\gamma', \epsilon_i, {i : choice+ l_j strong}) | \gamma' <- \gamma / l} -- (LabMisMatch2')                   
  (\gamma, (r1r2)_i) /^{level}l | \epsilon \in r1 = { (\gamma' ++ \gamma(fv(r2)) ++ { (i, \gamma(i)/l) } , (r1'r2)_i, \theta) | (\gamma', r1', \theta) <- (\gamma(fv(r1)), r1) /^{strong} l } ++  (\gamma(fv(r2)), r2) / l
                                | otherwise       = { (\gamma' ++ \gamma(fv(r2)) ++ { (i, \gamma(i)/l)}, (r1'r2)_i, \theta) | (\gamma', r1', \theta) <- (\gamma(fv(r1)), r1) /^{strong} l }
                                                                                                        -- (Pair2)
  (\gamma, (r1|r2)_i) /^{level} l   = (\gamma(fv(r1_i)), r1_i)/^{strong} l ++ (\gamma(fv(r2_i)), r2_i) /^{strong} l                  -- (Choice2)
  (\gamma, r*_i) /^{level} l       = { (\gamma', (r'r*)_i, \theta) | (\gamma', r', \theta) <- (\gamma, r) /^{strong} l } -- (Star2)
                    

Now the partial derivative operation is extended to handle the (\gamma, r) pairs.
The pderiv operation over (\gamma,r) pairs provides refinement suggestions \theta to those partial derivative cases which yield an empty set, 
ref to case (Eps1'), (LabMisMatch1'), (Eps2') and (LabMisMatch2').

The refinement suggestion \theta is defined as follows,

 \theta ::= { 1:rop_1, ..., n : rop_n }
                   where 1..n are labels 
 rop ::= (seq+ l_i level) | (choice+ l_i level)                     
 level ::= weak | strong                  

A refinement suggestion environment \theta is a set of mapping which maps regex src location i to recommendation operation rop.
There are two kinds of rops, sequence expansion seq+ or choice expansion choice+. The sequence expansion recommends to append l_i
to the src location.  e.g. let \theta_1 =  { 1 : seq+ b_2 weak }, r = a_1, then \theta_1(r) = a_1b_2
The choice expansion recommends to add l_i to the union. e.g. let \theta_2 = { 1 : choice+ b_2 weak}, r = a_1 then \tehta_1(r) = (a_1|b_2)
                  
The helper function 'max' returns the upper bound of two recommendation levels               
                  
 max strong _ = strong                  
 max _ strong = strong                   
 max weak weak = weak                   


Apart from the (\gamma, r) pairs extension, the pderiv op / is now parameterized by the {level} which stands for the level of recommendation. Let's ignore it for a while,
we will come back to it soon. 

* KEY IDEA #1: CHOOSING THE MINIMAL REFINEMENT BASED ON THE RESULTING NFA

Note that given a pattern r and a input word w where w \not \in r, we have  \theta_1 and  \theta_2
such that  \theta_1 \not\eq \theta_2 and w \in \theta_1(r) and w \in \theta_2(r). Let's consider the following example. 

Let r = (a|b)* and w = abc, we can either refinement r by extending the choice resulting (a|(b|c))* or a appending c after b resulting (a|(bc))*
TODO: show the full details of the refinmenet with the src loc.

Which one is better? of course we favor the minimal refinement. In a general settings, we of course will pick a \theta which is smaller in size 
(i.e. few changes). However as the above example highlights that there are situation where there are multiple \theta of the same size. 

One key idea is that the choice+ extension is favored because it leads to a smaller NFA (i.e. only a transition is added).
Whilst the seq+ is leading to a larger NFA (i.e. it adds a transition and a new state)


* KEY IDEA #2: CHOOISING THE REFEINEMENT BASED ON THE USER REQUIREMENT 

Let's consider an example,

let r = ((a)_1 | (b)_2), w = c

\gamma = { 1 : (.) }

we have two possible refinement recommendation, 

\theta_1 = { 1: (choice+ c_3 strong) }  -- note that the recommendataion level is taken into consideration
\theta_2 = { 2: (choice+ c_3 weak) }  


We favor \tehta_1 because as the user requirement enforces that src loc 1 should match at least one character (any character).


-}

-- partial derivative
  
  

class Accept t where
  accept :: t -> Doc -> Bool

instance Accept Re where
  accept r ls = any posEmpty $ foldl (\rs l -> pderiv r l) [r] ls 

instance Accept t => Accept [t] where
  accept rs ls = any (\r -> accept r ls) rs

type Doc = [Char]

getLabels :: Re -> [Int]
getLabels (Eps x)      = [x]
getLabels (Choice x rs) =  [x] ++ concatMap getLabels rs
getLabels (Pair x r1 r2) = [x] ++ (getLabels r1) ++ (getLabels r2)
getLabels (Star x r)   = [x] ++ (getLabels r)
getLabels (Ch x _)     = [x]
getLabels (Any x)      = [x]
getLabels Phi          = []



getLabel :: Re -> [Int]
getLabel (Eps x)      = [x]
getLabel (Choice x _) = [x]
getLabel (Pair x _ _) = [x]
getLabel (Star x _)   = [x]
getLabel (Ch x _)     = [x]
getLabel Phi          = []
getLabel (Any x)      = [x]

dontcare = (-999)


annotate :: Int -> Re -> Re
annotate i (Eps _) = Eps i
annotate i (Choice x cs) = Choice i cs
annotate i (Pair x r1 r2) = Pair i r1 r2
annotate i (Star x r) = Star i r
annotate i (Ch x c) = Ch i c
annotate i (Any x) = Any i
annotate i Phi = Phi


sigma :: Re -> String
sigma (Choice _ rs) = nub $ concat $ map sigma rs
sigma (Pair _ r1 r2) = nub $ (sigma r1) ++ (sigma r2)
sigma (Star _ r) = sigma r
sigma (Ch _ c) = [c]
sigma (Any _) = []
sigma Eps{} = []
sigma Phi = []

{-
* The Replacement Relation 
We use the following judgement to denote the replacement relation
$$ \gamma, r \turns w : q $$ 
where $\gamma$ is the user requirement, $r$ is the existing regular expression, $w$ is the input document and $t$ is the replacement regular expression.
It reads, under user requirement $\gamma$, $r$ can be replaced by $t$ which accepts $w$. 

There are two properties follows 

 1. $w \in r \Longrightarrow \Delta$ implies $ \Delta \vdash \gamma$ and $r \subseq t$.
 2. $w \not \in r$ implies $r \gamma\over\approximate t$  and $w \in t \Longrightarrow \Delta$ and $\Delta \vdash \gamma$.

The first property ensures that the replacement is subsuming the orginal regex $r$ if $w$ is already in $r$ and the matching result is conforming to the user requirement.
The second property ensures that if $w$ is not in $r$, the replacement shall have the same requirement-shape as the orginal one and conform to the user requirement. 
-}

replacement :: UReq -> Re -> Doc -> Re -> Bool 
{-
  i \in dom(\gamma) 
  w \in \gamma(i) 
  \gamma - {i}, r \vdash w, r'                           
 ----------------------------- (pExist)
  \gamma, r^i \vdash w : r'^i
-}
replacement ureq r w r' = 
   let ls = getLabel r  
       ls'  = getLabel r'          
   in ls == ls' && 
      replacement' ureq r w r' &&
        ( case ls of 
         { [] -> True
         ; (l:_) -> case lookup l ureq of 
             { Just r  -> w `match` [r]
             ; Nothing -> True } } )

{-
   i \not \in dom(\gamma)
   \gamma - {i}, r \vdash w : r'
 ------------------------------- (pIgnore)
 \gamma, r^i \vdash d : r'^i


   w \in r
 ------------------------- (rEmp)
 \gamma, () \vdash w : r

-}
replacement' ureq (Eps ls) w r' = w `match` [r']

{-
   d \in r 
 ------------------------- (rLab)
 \gamma, l \vdash d : r
-}

replacement' ureq (Ch ls c) w r' = w `match` [r']


{-
   d \in r 
 ------------------------- (rAny)
 \gamma, . \vdash d : r
-}

replacement' ureq (Any ls) w r' = w `match` [r']


{-
  fv(r1) = \bar{i1} fv(r2 = \bar{i2} 
 \gamma_{\bar{i1}}, r1 \vdash d1 : r1'                              
 \gamma_{\bar{i2}}, r2 \vdash d2 : r2'                         
 ------------------------------------- (rSeq)
 \gamma, r1r2 \vdash d1d2 : r1'r2'
-}
replacement' ureq (Pair ls r1 r2) w (Pair ls' r1' r2') = 
   let ls1 = getLabels r1   
       ls2 = getLabels r2         
       ureq1 = limit ureq ls1 
       ureq2 = limit ureq ls2
       ws    = split2 w
   in any (\(w1,w2) -> replacement ureq1 r1 w1 r1' && replacement ureq2 r2 w2 r2' ) ws




{-

                                     

 we use \gamma_{\bar{i}} to denote { (i,\gamma(i)) | i \in \bar{i} and i \in dom(\gamma) }
                          
                          
  \gamma, r1 \vdash d : r1'
 -------------------------------------- ( rOr1)   
 \gamma, r1|r2 \vdash d : r1'|r2     


  \gamma, r2 \vdash d : r2'
 -------------------------------------- ( rOr2)   
 \gamma, r1|r2 \vdash d : r1|r2'                          

-}


replacement' ureq (Choice ls rs) w (Choice ls' rs') = replChoiceSub rs rs'
   where replChoiceSub [] rs = w `match` rs
         replChoiceSub _ [] = False
         replChoiceSub (r:rs) (r':rs') = replacement ureq r w r' || replChoiceSub rs rs'

{-

  \gamma, r \vdash di : r'  \forall i \in {1,n}
 ------------------------------------------------- ( rStar)   
 \gamma, r* \vdash d1...dn : r'*                          
-}
replacement' ureq (Star ls r) w (Star ls' r') =
  let wss = split w
  in any (\ws -> all (\w' -> replacement ureq r w' r') ws) wss



{- Rules rSeq, rOr1, rOr2 and rStar validate the replacement relation indeterministically



  \gamma,p \vdash d:p'    \forall d\in D 
 ---------------------------------------- (pDocS)
  \gamma p \vdash D : p'
-}

split2 :: String -> [(String,String)]
split2 [] = [ ([],[]) ]
split2 (w@(c:ws)) = 
       nub $ (w,[]) : ([],w) : 
             (map (\(w1,w2) -> (c:w1,w2)) $ split2 ws)

split :: String -> [[String]]
split [] = [ [] ]
split [c] = [ [[c]] ]
split (w@(c:ws)) = 
 [w]:[ take i w : xs | i <- [1..length ws], xs <- split (drop i w) ]


match :: [Char] -> [Re] -> Bool
match cs rs = let finals = foldl (\ts c -> concatMap (\t -> pderiv t c) ts) rs cs
              in  any posEmpty finals


{-
 * The Refinement Algorithm 

Naively, we use the judgement 
$$\gamma,p \models d : q $$ 
to denote the refinement algorithm. 


However this is NOT going to work, consider the following example

\gamma = { (1 : .+ ) (2 : .+) }
r = ((A*)(A*))
 or in explicit annotation
r = (0 :: ( (1 :: A*) (2 :: A*)))

d = A

Note that r is ambigous. If we send A to (1 :: A*), we have the result
\gamma = { (1 : .* ) (2 : .+) } and r = ((A*),(A*)) as we not only 
consume the A in (1:: A*), but also update \gamma.

If we send A to (2 :: A*), the resulting pair will be different
\gamma = { (1 : .+ ) (2 : .*) } and r = ((A*),(A*))

In summary, when we perform partial derivative operation, the \gamma and the r go
together in pairs.

Hence we use the judgement
$${ (\gamma_1,p_1), ..., (\gamma_n,p_n) } \models d : {q_1,...,q_m} $$ 

where 
${ (\gamma_1,p_1), ..., (\gamma_n,p_n) }$ are the user requirement and orginal 
sub regex (nfa state) pairs. ${q_1,...,q_m}$ denotes the output set of 
refined sub regex (nfa state).





The algorithm correctness property (Soundness)

Let $\gamma$ be the user requirement, $r$ denote the initial regular expression pattern, $w$ denote the input document
$ { \gamma, r } \models d : { r1', ... , rn' } $ implies $\gamma, r \vdash d : r1'|...|rn'$.

-}


-- r0 = A*

r0 = Star 1 (Ch 2 'A')

                          
-- r1 = (A|B)*

r1 = Star 1 (Choice 2 [Ch 3 'A', Ch 4 'B'])

-- r2 = (A|B|C)*

r2 = Star 1 (Choice 2 [Ch 3 'A', Ch 4 'B', Ch 5 'C'])




r3 = Pair 1 (Ch 2 'A') (Ch 3 'B')

-- r4 = ()

r4 = Eps 1 

-- t3 = .+

t3 = Pair dontcare (Choice dontcare [Ch dontcare 'A',Ch dontcare 'B',Ch dontcare 'C']) (Star dontcare (Choice dontcare [Ch dontcare 'A',Ch dontcare 'B',Ch dontcare 'C']))

t4 = Pair dontcare (Choice dontcare [Ch dontcare 'A',Ch dontcare 'B']) (Star dontcare (Choice dontcare [Ch dontcare 'A',Ch dontcare 'B']))


v = "ABC"

g1 = [(1::Int, t3)]

g2 = [(1::Int, t4)]

{-
w = <h><d>65103020</d></h>
r5 = .*<s>([0-9]+)</s>.*
g5 = [(1::Int, [0-9]+)]
-}

-- anySym x = Choice [x] (map (\i -> (Ch [(100*x+i)] (chr i))) ([47,60,62] ++ [100,104])) 

-- anySym x = Choice [x] (map (\i -> (Ch [(100*x+i)] (chr i))) [0..128]) 

anySym x = Any x


anyNum x = Choice x (map (\i -> (Ch (100*x+i) (chr i))) [48..57]) 

w = "<h><d>91234567</d></h>"
r5 = Pair 1 p1 (Pair 2 p2 (Pair 3 p3 (Pair 4 p4 p5)))
  where p1 = Star 20 (anySym 30) 
        p2 = Pair 41 (Ch 42 '<') (Pair 43 (Ch 44 's') (Ch 45 '>'))
        p3 = Star 50 (anyNum 51)
        p4 = Pair 61 (Ch 62 '<') (Pair 63 (Ch 64 '/') (Pair 65 (Ch 66 's') (Ch 67 '>')))
        p5 = Star 70 (anySym 80)
g5 = [(50::Int, Pair 0 (anyNum 90) (Star 0 (anyNum 90)))]



w' = "<head><div>91234567</div></head>"
r5' = Pair 1 p1 (Pair 2 p2 (Pair 3 p3 (Pair 4 p4 p5)))
  where p1 = Star 20 (anySym 30) 
        p2 = Pair 41 (Ch 42 '<') (Pair 43 (Ch 44 's') (Ch 45 '>'))
        p3 = Star 50 (anyNum 51)
        p4 = Pair 61 (Ch 62 '<') (Pair 63 (Ch 64 '/') (Pair 65 (Ch 66 's') (Ch 67 '>')))
        p5 = Star 70 (anySym 80)
g5' = [(50::Int, Pair 0 (anyNum 90) (Star 0 (anyNum 90)))]
g5'' = [(50::Int, Pair 0 (anySym 90) (Star 0 (anySym 90)))]

{-
w1 = (A)
r6 = <(A|B)*>
-}

w1 = "(A)"
r6 = Pair 0 
      (Ch 1 '<') 
      (Pair 2 (Star 3 (Choice 4 [(Ch 5 'A'),(Ch 6 'B')]))
          (Ch 7 '>'))
g6 = [(3::Int, r1)]


{-
w2 = (A)
r7 = .*<(A|B)*>.*

there are still some space for pruning

sortBy (\x y -> compareREnv (snd x) (snd y) )  (ref' [(g7,r7, IM.empty)] "(A)") !! 0
sortBy (\x y -> compareREnv (snd x) (snd y) )  (ref' [(g7,r7, IM.empty)] "(A)") !! 1
sortBy (\x y -> compareREnv (snd x) (snd y) )  (ref' [(g7,r7, IM.empty)] "(A)") !! 2
sortBy (\x y -> compareREnv (snd x) (snd y) )  (ref' [(g7,r7, IM.empty)] "(A)") !! 3
sortBy (\x y -> compareREnv (snd x) (snd y) )  (ref' [(g7,r7, IM.empty)] "(A)") !! 4

-}


w2 = "(A)"
r7 = Pair (-10)
      (Star (-20) (Choice (-21) [Ch (-22) 'A', Ch (-23) 'B', Ch (-24) '<', Ch (-25) '>']))
      (Pair (-30) 
       (Pair 0 
        (Ch 1 '<') 
        (Pair 2 (Star 3 (Choice 4 [(Ch 5 'A'),(Ch 6 'B')]))
          (Ch 7 '>')))
       (Star (-40) (Choice (-41) [Ch (-42) 'A', Ch (-43) 'B', Ch (-44) '<', Ch (-45) '>']))
      )
g7 = [(3::Int, r1)]


{-
hasStrong :: REnv -> Bool
hasStrong renv = let rops = concatMap snd (IM.toList renv)
                 in any isStrong rops
-}

{-
main :: IO ()
main = do 
  [si] <- getArgs
  let i = read si
  print $ pretty r5        
  print $ pretty $ (refine g5 r5 w) !! i
-}

{-
New idea: refinement algo takes ureq re pair and the input words returns a set of 

```
----------------------------------------------------------------------------------------------------------------------------------- (Eps)
\overline{ \gamma, r, \Psi } |=  \epsilon: { \Psi | (\gamma, r, \Psi) \in \overline{ \gamma, r, \Psi }, \epsilon \in \Psi(r)  } ++ 
                                           { \Psi . (i -> +\epsilon, s) } | (\gamma, r, \Psi) \in  \overline{ \gamma, r, \Psi } }
      
      
      
\overline{ \gamma, r, \Psi } / l = \overline { \gamma', r', \Psi' } 
\overline { \gamma', r', \Psi o \Psi'  } |= w: \overline {\Psi''} 
----------------------------------------------------------------------------------------------------------------------------------- (Ind)
\overline{ \gamma, r, \Psi } |=  lw : {\Psi''}
      
```

Note that from (Ind) the refinement environment \Psi is passed along
-}

data REnv = REnv { ops :: IM.IntMap RS
                 , countMkFin :: Int
                 , countStrongATr :: Int
                 , countStrongASt :: Int
                 , countStrongNoCh :: Int                   
                 , countWeakATr :: Int
                 , countWeakASt :: Int
                 , countWeakNoCh :: Int                   
                 } 
          deriving (Show, Eq, Ord)
            
data RS = RS { atrs :: Set.IntSet
             , asts :: [ROp]
             , mkfin :: Int -- mkfin is always weak?!
             , strong_atrs :: Int
             , strong_asts :: Int
             , strong_noch :: Int
             , weak_atrs :: Int
             , weak_asts :: Int
             , weak_noch :: Int
             } 
        deriving (Show, Eq, Ord)

                 
          
emptyRS = RS Set.empty [] 0 0 0 0 0 0 0

emptyREnv = REnv IM.empty 0 0 0 0 0 0 0


singletonRS :: ROp -> RS
singletonRS rop | rop `div` 1000 == 0 = RS (Set.singleton rop) [] 0 1 0 0 0 0 0
singletonRS rop | rop `div` 1000 == 1 = RS (Set.singleton rop) []   0 0 0 0 1 0 0
singletonRS rop | rop `div` 1000 == 2 = RS Set.empty [rop]        0 0 1 0 0 0 0
singletonRS rop | rop `div` 1000 == 3 = RS Set.empty [rop]          0 0 0 0 0 1 0
singletonRS rop | rop `div` 1000 == 4 = RS Set.empty []               1 0 0 0 0 0 0
singletonRS rop | rop `div` 1000 == 5 = RS Set.empty []               1 0 0 0 0 0 0
singletonRS rop | rop `div` 1000 == 6 = RS Set.empty []            0 0 0 1 0 0 0
singletonRS rop | rop `div` 1000 == 7 = RS Set.empty []              0 0 0 0 0 0 1


lookupREnv :: SrcLoc -> REnv -> Maybe RS
lookupREnv i renv = IM.lookup i (ops renv)
                    


deleteREnv :: SrcLoc -> REnv -> REnv
deleteREnv i renv =               
  case IM.lookup i (ops renv) of
    { Nothing -> renv
    ; Just rs -> let ops'            = IM.delete i (ops renv) 
                     countMkFin'     = countMkFin renv - mkfin rs
                     countStrongATr' = countStrongATr renv - strong_atrs rs
                     countStrongASt' = countStrongASt renv - strong_asts rs
                     countStrongNoCh' = countStrongNoCh renv - strong_noch rs
                     countWeakATr'   = countWeakATr renv - weak_atrs rs 
                     countWeakASt'   = countWeakASt renv - weak_asts rs
                     countWeakNoCh'  = countWeakNoCh renv - weak_noch rs
                 in REnv ops'  countMkFin' countStrongATr' countStrongASt' countStrongNoCh' countWeakATr' countWeakASt' countWeakNoCh'
    }
  
  
singletonREnv :: SrcLoc -> RS -> REnv
singletonREnv l rs = 
  REnv (IM.singleton l rs)  (mkfin rs) (strong_atrs rs) (strong_asts rs) (strong_noch rs) (weak_atrs rs) (weak_asts rs) (weak_noch rs)

-- reloc : relocate rop under l' to l in a renv

reloc :: SrcLoc -> SrcLoc -> REnv -> REnv
reloc l' l renv  =
  let ops_ = ops renv
  in case IM.lookup l' ops_ of
    { Just rs' -> 
         let renv1 = deleteREnv l' renv
             renv2 = singletonREnv l rs' 
         in combineREnv renv1 renv2
    ; Nothing  -> renv
    }
              
  
combineRS :: RS -> RS -> RS
combineRS rs1 rs2 = 
  let atrs' = ((atrs rs1) `Set.union` (atrs rs2)) 
      asts' = (asts rs1) ++ (asts rs2)
      mkfin' = mkfin rs1 + mkfin rs2
      (s_atrs',w_atrs') = Set.partition isStrong atrs'
      strong_atrs' = Set.size s_atrs'
      strong_asts' = strong_asts rs1 + strong_asts rs2
      weak_atrs'   = Set.size w_atrs'
      weak_asts'   = weak_asts rs1  + weak_asts rs2
      strong_noch' = strong_noch rs1 + strong_noch rs2 + (strong_atrs rs1 + strong_atrs rs2 - strong_atrs')
      weak_noch'   = weak_noch rs1 + weak_noch rs2 + (weak_atrs rs1 + weak_atrs rs2 - weak_atrs')
  in atrs' `seq` asts' `seq` mkfin' `seq` strong_atrs' `seq` strong_asts' `seq` strong_noch' `seq` weak_atrs' `seq` weak_asts' `seq` weak_noch'
     `seq` RS  atrs' asts' mkfin' strong_atrs'  strong_asts' strong_noch' weak_atrs' weak_asts' weak_noch' 
  

-- combine two REnv
combineREnv :: REnv -> REnv -> REnv 
combineREnv renv1 renv2 = 
  let ops_ = {-# SCC "ops_" #-} IM.unionWith (\x y -> (x `combineRS` y)) (ops renv1) (ops renv2)
      (countStrongATr_, countWeakATr_, countStrongNoCh_, countWeakNoCh_) = 
        {-# SCC "foldl" #-}
            ops_ `seq`
            IM.foldl' go (0::Int,0::Int,0::Int,0::Int) ops_
            -- go2 (#0::Int,0::Int,0::Int,0::Int#) ops__
      countStrongASt_ = countStrongASt renv1 + countStrongASt renv2
      countMkFin_ = countMkFin renv1 + countMkFin renv2
      countWeakASt_ = countWeakASt renv1 + countWeakASt renv2
  in REnv ops_  countMkFin_ countStrongATr_ countStrongASt_  countStrongNoCh_ countWeakATr_ countWeakASt_ countWeakNoCh_
     where       
       go :: (Int, Int, Int, Int) -> RS ->  (Int, Int, Int, Int)
       go (s,w,sn, wn) rs =
         let 
           s' = rs `seq` s + strong_atrs rs
           w' = w + weak_atrs rs
           sn' = sn + strong_noch rs
           wn' = wn + weak_noch rs
         in s' `seq` w' `seq` sn' `seq` wn' `seq` (s', w', sn', wn')
       go2 :: (#Int, Int, Int, Int#) -> [(Int,RS)] ->  (#Int, Int, Int, Int#)
       go2 (#s,w,sn, wn#) ((k,rs):krs) =
         let 
           s' = rs `seq` s + strong_atrs rs
           w' = w + weak_atrs rs
           sn' = sn + strong_noch rs
           wn' = wn + weak_noch rs
         in {- s' `seq` w' `seq` sn' `seq` wn' `seq` -} go2 (#s', w', sn', wn'#) krs
       go2 (#s,w,sn, wn#) [] = (#s,w,sn, wn#)

  

type ROp = Int 

data ROpType = RATr | RASt | RMkFin | RNoCh

opType :: ROp -> ROpType
opType rop =
       let bit = rop `div` 1000
       in if (bit == 0) || (bit == 1)
          then RATr
          else if (bit == 2) || (bit == 3)
               then RASt
               else if (bit == 4) || (bit == 5)
                    then RMkFin
                    else RNoCh
          
reInROp :: ROp -> Maybe Re
reInROp rop =
  let bit = rop `div` 1000
  in if (bit < 4)
     then 
       let bits = rop `mod` 1000
           ch = chr bits
       in Just (Ch 0 ch)
     else Nothing
        
          
resInROps :: [ROp] -> [Re]
resInROps rops = map (\(Just x) -> x) (filter isJust (map reInROp rops))

resInREnv :: REnv -> [Re]
resInREnv renv = 
  let rss = map snd (IM.toList (ops renv))
      atrss = concatMap (Set.toList . atrs) rss
      astss = concatMap asts rss
  in resInROps (atrss ++ astss) 


compareREnv :: REnv -> REnv -> Ordering
compareREnv r1 r2 = 
  let c1   = renvSize r1
      c2   = renvSize r2
      sNc1 = countStrongNoCh r1
      sNc2 = countStrongNoCh r2
      sTr1 = countStrongATr r1  
      sTr2 = countStrongATr r2
      sSt1 = countStrongASt r1
      sSt2 = countStrongASt r2
      sMF1 = countMkFin r1
      sMF2 = countMkFin r2
      wNc1 = countWeakNoCh r1
      wNc2 = countWeakNoCh r2
      wTr1 = countWeakATr r1  
      wTr2 = countWeakATr r2
      wSt1 = countWeakASt r1
      wSt2 = countWeakASt r2

  in comparePairs [ (c1,c2)
                  , ((sNc2 + wNc2), (sNc1 + wNc1))
                  , (sNc2, sNc1)
                  , (sTr2, sTr1)
                  , (wTr2, wTr1)
                  , (sSt2, sSt1)
                  , (wSt2, wSt1)
                  , (sMF2, sMF1)
                  ]
   
comparePairs [] = EQ
comparePairs ((x,y):rest) = 
  case compare x y of
    EQ -> comparePairs rest
    otherwise -> otherwise
                      
   {-
   case compare c2 c1 of
    { EQ -> case compare sNc1 sNc2 of
         { EQ -> case compare sTr1 sTr2 of
              { EQ -> case compare sSt1 sSt2 of
                   { EQ -> case compare sMF1 sMF2 of
                        { EQ -> case compare wNc1 wNc2 of 
                             { EQ -> case compare wTr1 wTr2 of
                                  { EQ -> compare wSt1 wSt2 
                                  ; others -> others }
                             ; others -> others }
                        ; others -> others }
                   ; others -> others }  
              ; others -> others }
         ; others -> others }
    ; others -> others }
     -}


-- count the number of ROps in renv


renvSize :: REnv -> Int
renvSize renv = (countStrongNoCh renv + countWeakNoCh renv + countStrongATr renv + countStrongASt renv + countMkFin renv + countWeakATr renv + countWeakASt renv)

{-
renvSize :: REnv -> Int
renvSize renv = sum (map (\ (k,v) -> length v) (IM.toList renv))

renvStrong :: REnv -> Int
renvStrong renv = sum (map (\ (k,v) -> length (filter isStrong v)) (IM.toList renv))

renvWeak :: REnv -> Int
renvWeak renv = sum (map (\ (k,v) -> length (filter isWeak v)) (IM.toList renv))

renvRASt :: REnv -> Int
renvRASt renv = sum (map (\ (k,v) -> length (filter isRASt v)) (IM.toList renv))

countStrongATr :: REnv -> Int 
countStrongATr renv = sum (map (\ (k,v) -> length (filter (\x -> (isStrong x) && (isRATr x)) v)) (IM.toList renv))

countStrongASt :: REnv -> Int 
countStrongASt renv = sum (map (\ (k,v) -> length (filter (\x -> (isStrong x) && (isRASt x)) v)) (IM.toList renv))

countStrongNoCh :: REnv -> Int 
countStrongNoCh renv = sum (map (\ (k,v) -> length (filter (\x -> (isStrong x) && (isRNoCh x)) v)) (IM.toList renv))

countStrongMkFin :: REnv -> Int 
countStrongMkFin renv = sum (map (\ (k,v) -> length (filter (\x -> (isStrong x) && (isMkFin x)) v)) (IM.toList renv))



countWeakATr :: REnv -> Int 
countWeakATr renv = sum (map (\ (k,v) -> length (filter (\x -> (isWeak x) && (isRATr x)) v)) (IM.toList renv))

countWeakASt :: REnv -> Int 
countWeakASt renv = sum (map (\ (k,v) -> length (filter (\x -> (isWeak x) && (isRASt x)) v)) (IM.toList renv))

countWeakNoCh :: REnv -> Int 
countWeakNoCh renv = sum (map (\ (k,v) -> length (filter (\x -> (isWeak x) && (isRNoCh x)) v)) (IM.toList renv))

countWeakMkFin :: REnv -> Int 
countWeakMkFin renv = sum (map (\ (k,v) -> length (filter (\x -> (isWeak x) && (isMkFin x)) v)) (IM.toList renv))
-}                         
                         
isStrong :: ROp -> Bool
isStrong rop = even (rop `div` 1000)

isWeak :: ROp -> Bool
isWeak rop = odd (rop `div` 1000)

isRATr :: ROp -> Bool
isRATr rop = let bit = rop `div` 1000
             in (bit == 0) || (bit == 1)

isRASt :: ROp -> Bool
isRASt rop = let bit = rop `div` 1000
             in (bit == 2) || (bit == 3)

isRNoCh :: ROp -> Bool
isRNoCh rop = let bit = rop `div` 1000
              in (bit == 4) || (bit == 5)

isMkFin :: ROp -> Bool
isMkFin rop = let bit = rop `div` 1000
              in (bit == 6) || (bit == 7)
                       
                       
data RLevel = Strong | Weak deriving (Ord, Eq, Show)

{-
renv_1 \entails renv_2 iff 
   \forall l in renv_2 s.t. renv_1(l) superseteq renv_2(l)   

 note the equality among ROp we ignore the loc of the Re
-}



{- TODO fix me later, we might need entailment relation again. 

entail :: REnv -> REnv -> Bool 
entail r1 r2 = 
  let ks = IM.keys r2
  in all (\k -> case (IM.lookup k r1, IM.lookup k r2) of
            { (Just rs1, Just rs2) -> rs1 `ropSubsume` rs2
            ; (_,_) -> False } ) ks

ropSubsume :: [ROp] -> [ROp] -> Bool
ropSubsume rs1 rs2 = all (\r2 -> r2 `elem` rs1) rs2
-}

-- top level function

refine :: UReq -> Re -> S.ByteString -> [Re]
refine ureq r cs = 
  let cmap = choiceMap r 
      renvs = nub $ sortBy compareREnv (ref [(cmap, ureq, r, emptyREnv)] cs)
      -- io = renvs `seq` logger ("refine "++ (show $ map (\renv -> " | " ++ show renv  ) renvs))
  in {- io `seq` -} 
     map (\renv ->  apply_ renv r)  renvs

-- the main routine
-- calling urepderiv to apply the R|-^L r/l => { R,r,\sigma } over l1,...,ln
-- the \sigma(s) are propogated by urepderiv 
-- we also prune away redundant states
-- 

ref :: [(ChMap, UReq, Re, REnv)] -> S.ByteString -> [REnv]
ref urs bs = case S.uncons bs of
  { Nothing ->
        [ renv | (cmap, ureq, r, renv) <- urs, posEmpty {- (renv `apply_` r)-}  r ] ++      
        [ renv' `combineREnv` renv   -- try to fix those states which are non-final?
        | (cmap, ureq, r, renv) <- urs
        , renv' <- mkFin r
        , not (posEmpty {- (renv `apply_` r) -} r)
        , any (\i -> case lookupUR i ureq of
                  { Nothing -> False
                  ; Just t  -> posEmpty t }) (getLabel r) ]
  ; Just (l,w) ->
         let urs' =  prune5 $ concatMap (\ (cmap, ur,r,renv) ->  {- prune3 r $ -} urePDeriv (cmap, ur, r, renv) l) urs 
             io = logger $ S.length bs -- logger ("ref " ++ (l:w) ++ (show $ map (\(_,r,renv) -> pretty r ++ "|" ++ show renv) urs) )  
         in  {- io `seq` -} urs' `seq` ref urs' w
  }

{-
pruning by checking for entailment among REnvs, looking for local optimal

this pruning is not working. see

(A+B)*(B)(C*)

matching "DDC"

where UReq = [(3, C*)]

rops_1 = [(0, ATr D), (0, ATr C)]

rops_2 = [(0, ATr D), (1, ATr D)]

rops_2 should be favored because C is matched with 3 which is under the UReq

however, with this pruning scheme, rops_2 is pruned at the 2nd D input character, before the 'C' is considered.
as rops_1 = [(0, ATr D) ]  is entailed by rops_2 = [(0, ATr D), (1, ATr D)] 
-}

{-
prune :: [(UReq, Re, REnv)] -> [(UReq, Re, REnv)]
prune ts = let sts = sortBy (\(_,_,r1) (_,_,r2) -> compare (renvSize r2) (renvSize r1)) ts
           in prune' sts


prune' :: [(UReq, Re, REnv)] -> [(UReq, Re, REnv)]
prune' [] = []
prune' (x:xs) | any (\y -> (trd x) `entail` (trd y)) xs = prune' xs
              | otherwise = (x:(prune' xs))
-}
trd :: (a,b,c) -> c
trd (_,_,x) = x



{-
prune by semantic equivalent 
too expensive!
-}

prune2 :: Re -> [(UReq, Re, REnv)] -> [(UReq, Re, REnv)]
prune2 r [] = []
prune2 r (x:xs) | any (\y -> containGTE r x y) xs = prune2 r xs
                | otherwise = x:(prune2 r xs)
  where containGTE r x y = let ex = trd x 
                               ey = trd y                                
                           in (apply_ ex r) `equiv` (apply_ ey r) && (compareREnv ex ey >= EQ) 


{-
prune by isomorphism.

Let r be a regular expression, (l1, rops1) and (l2, rops2) Label-ROp pairs, they are considered iso w.r.t to r iff
   1) l1 == l2 and rops1 == rops2 or
   2) l1 and l2 are labels of the two alternatives of the choice sub-exp in r

e.g. r = (Choice [1] (Ch [2] 'A') (Ch [3] 'B'))

 (2, ATr (Ch [4] 'C')) and (3, ATr (Ch [5] 'C')) are considered iso w.r.t to r.
-}


-- Rationale: applying the above two operations lead to the semantically equivalent regex
{- TODO: fixme later
prune3 :: Re -> [(UReq, Re, REnv)] -> [(UReq, Re, REnv)]
prune3 r [] = [] 
prune3 r (x:xs) | any (\y -> iso r (trd x) (trd y)) xs = prune3 r xs
                | otherwise = x:(prune3 r xs)
  where iso r renv_x renv_y 
          | (IM.size renv_x /= IM.size renv_y) = False
          | otherwise =  
              let ps1 = IM.toList renv_x
                  ps2 = IM.toList renv_y
              in isoPairs r ps1 ps2
        isoPairs r [] [] = True
        isoPairs r _  [] = False
        isoPairs r [] _  = False
        isoPairs r ((lx,x):xs) ((ly,y):ys)  -- assumption, IM.toList sort by the keys
           | lx == ly  = (x == y) && (isoPairs r xs ys)
           | choiceAlts r lx ly = (x == y) && (isoPairs r xs ys)
           | otherwise = False

-- ^ prune by duplicated rop, -- not effective, slower

prune4 :: [(UReq, Re, REnv)] -> [(UReq, Re, REnv)]
prune4 [] = []
prune4 ((x@(_,_,renv)):xs) | hasDupROps renv = prune4 xs
                           | otherwise = x:(prune4 xs)

hasDupROps :: REnv -> Bool 
hasDupROps renv = let ps = IM.toList renv 
                  in any (\(k,rops) -> 
                      let rops' = filter (not . isRNoCh) rops 
                      in length (nub rops') /= length rops')  
                     ps
-}
                     
-- ^ prune by common partial derivatives (state), choose one local optimal renv                     

prune5 :: [(ChMap, UReq, Re, REnv)] -> [(ChMap, UReq, Re, REnv)]
prune5 ures = 
  let grouped = -- | re -> (ureq, re, renv)
        foldl' (\m (cmap, ureq, re, renv) -> 
                case M.lookup re m of 
                  { Nothing -> M.insert re (cmap, ureq,re,renv) m 
                  ; Just (_,_,_,renv') -> case compareREnv renv renv' of
                    { LT -> M.update (\_ -> Just (cmap, ureq,re,renv)) re m 
                    ; _  -> m 
                    }
                  } ) M.empty ures
  in map snd (M.toList grouped)
                                           
                    

-- check whether the two labels are siblings under the choice sub-exp in r

choiceAlts :: Re -> Int -> Int -> Bool 
choiceAlts (Choice _ rs) x y = 
     let ls = concatMap getLabels rs  
     in x `elem` ls && y `elem` ls
choiceAlts (Pair _ r1 r2) x y = choiceAlts r1 x y || choiceAlts r2 x y
choiceAlts (Star _ r) x y  = choiceAlts r x y 
choiceAlts (Ch _ _) _ _ = False
choiceAlts (Eps _ ) _ _ = False
choiceAlts Phi      _ _ = False
choiceAlts (Any _ ) _ _ = False

type ChMap = IM.IntMap [Re]


choiceMap :: Re -> IM.IntMap [Re]
choiceMap (Choice _ rs) = foldl' (\m r -> IM.insert (head $ getLabel r) rs m) IM.empty rs
choiceMap (Pair _ r1 r2) = 
  let im1 = choiceMap r1 
      im2 = choiceMap r2
  in im1 `seq` im2 `seq` im1 `IM.union` im2
choiceMap (Star _ r) = choiceMap r     
choiceMap _ = IM.empty


urePDeriv :: (ChMap, UReq, Re, REnv) -> Char -> [(ChMap, UReq, Re, REnv)]
urePDeriv (cmap, ur, r, psi) l = 
  let 
      max_i = maximum $ (getLabels r) ++ (concatMap getLabels $ resInREnv psi)
      (t,e) = run (Env max_i) (urPDeriv (ur, r) l Weak)
  in t `seq` [ (cmap, ur', r''', psi'' `combineREnv` psi) | (ur', r', psi') <- t,  -- let r''' = r', let psi'' = psi' ] 
               -- let r'' = r', -- run_ e (psi' `apply` r'),  -- we can only apply simplification after we apply psi' to r' 
               let (r''',psi'') = {- io `seq` -} simpl  r' psi' ,
               not (redundantREnv psi'' cmap) ] 
     -- not (isRedundant psi r psi'' r''' ) ] -- e.g. adding 'a' to (a|b), since there already an 'a' -- can't just check whether r \equiv r''' , because there are RNoCh rops


-- check whether REnv is redundant w.r.t to r
redundantREnv :: REnv -> ChMap -> Bool
redundantREnv renv cmap = 
  let srcAndOps = IM.toList (ops renv)
  in any (\(src,ops) -> redundantOps src ops cmap) srcAndOps
     where redundantOps :: SrcLoc -> RS -> ChMap -> Bool
           redundantOps i rs cmap = 
             let aTrOps = Set.toList (atrs rs)
             in any (\aTrOp -> redundantRATr i aTrOp cmap) aTrOps
                -- check whether (i, {RATr l}) is redundant
                -- since i is a leaf node in r
                -- the rop is redunant if l is already sibling under the choice + operator w.r.t i in r.
                -- e.g.  (2, RAtr (3:a)) is redundant w.r.t to (1:a+2:b)
           redundantRATr :: SrcLoc -> ROp -> ChMap -> Bool 
           redundantRATr i rop cmap = 
             case (reInROp rop, IM.lookup i cmap) of
               { (Just r, Just rs) -> r `elem` rs
               ; _ -> False
               } 
           
choiceSiblings :: Re -> SrcLoc -> [Re]
choiceSiblings (Choice _ rs) i | i `elem` (concatMap getLabel rs) = rs -- TODO:  choice can be nested.
                               | otherwise = concatMap (\r -> choiceSiblings r i) rs
choiceSiblings (Pair _ r1 r2) i = choiceSiblings r1 i ++ choiceSiblings r2 i
choiceSiblings (Star _ r) i = choiceSiblings r i
choiceSiblings _ _ = []

{-
isRedundant :: REnv -> Re -> REnv -> Re -> Bool 
isRedundant renv1 r1 renv2 r2 = 
  let diff = diffREnv renv2 renv1
  in -- (not (all isRNoCh diff)) && (r1 `equiv` r2) 
     -- checking for (r1 `equiv` r2) is expensive
     (any (\(k, rops) -> any (not . isRNoCh) rops) (IM.toList diff)) && bogusDiff diff r1
   where bogusDiff diff (Choice (l:_) rs) = -- the diff is bogus if it is applied to r1, it does not change the semantics e.g. adding 'a' to (a+b)
           case IM.lookup l diff of              
            { Just rops -> any (\(RATr r _) -> r `elem` rs) rops
            ; Nothing -> False }  
         bogusDiff diff (Pair _ r1 r2) = bogusDiff diff r1 || bogusDiff diff r2
         bogusDiff diff (Star _ r) = bogusDiff diff r
         bogusDiff diff (Ch _ _) = False
         bogusDiff diff (Any _) = False
         bogusDiff diff (Eps _) = False
         bogusDiff diff Phi = False

diffREnv :: REnv -> REnv -> REnv -- rops in r2 but not in r1
diffREnv r2 r1 = 
 let ps = IM.toList r2  
     ps' = foldl (\acc (k,rops) -> case IM.lookup k r1 of
      { Nothing -> acc ++ [(k,rops)]
      ; Just rops' -> acc ++ [(k,filter (\rop -> not (rop `elem` rops')) rops)] } ) [] ps
 in IM.fromList ps'
-}



-- finding the maximal among two RLevels

maximal :: RLevel -> RLevel -> RLevel
maximal Strong _ = Strong
maximal _ Strong = Strong
maximal _ _ = Weak
{-
newtype State s a = State { runState :: (s -> (a,s)) } 
 
instance Monad (State s) where
  return a        = State (\s -> (a,s))
  (State x) >>= f = State (\s -> let (a,s') = x s 
                                     stb = f a
                                 in (runState stb) s')

-}
run :: s -> State s a -> (a,s)
run s sta = (runState sta) s


run_ :: s -> State s a -> a
run_ s sta = fst $ run s sta

data Env = Env { maxId :: Int
               } deriving Show



setMaxId :: Int -> State Env ()
setMaxId i = state (\env -> let env' = env{maxId = i}
                            in ((), env'))


getMaxId :: State Env Int
getMaxId = state (\env -> (maxId env,env)) 

incMaxId :: State Env Int
incMaxId = do 
 { max_i <- getMaxId 
 ; let next_i = max_i + 1
 ; setMaxId next_i                    
 ; return next_i 
 }



urPDeriv :: (UReq, Re) -> Char -> RLevel -> State Env [(UReq, Re, REnv)]
urPDeriv (ur, Eps i) l rlvl
  | i `inUR` ur = do 
     { next_i <- incMaxId
       -- let next_i  = i  
     ; return [ ((updateUR i r' ur), Eps next_i, singletonREnv i (singletonRS {- (RASt (Ch next_i l) Strong) -} (2000+(ord l)) )) 
              | let r = fromJust (lookupUR i ur), r' <- pderiv r l ] 
     }
  | otherwise   = do 
     { next_i <- incMaxId 
       -- let next_i  = i    
     ; return [ (ur, Eps next_i, singletonREnv i (singletonRS {- (RASt (Ch next_i l) (maximal rlvl Weak)) -} (case rlvl of { Weak -> (3000+(ord l))  ; Strong -> (2000+(ord l)) })  )) ]
     }
urPDeriv (ur, (Ch i l)) l' rlvl = 
  case lookup i ur of 
    { Just r | l == l' -> do 
      { -- next_i <- incMaxId
      ; return  [ ((updateUR i r' ur), (Eps i), singletonREnv i (singletonRS {- (RNoCh Strong) -} 6000 ))
                | r' <- pderiv r l ]
      }
             | l /= l' -> do 
      { -- next_i <- incMaxId
      ; next_i2 <- incMaxId
      ; return  [ ((updateUR i r' ur), (Eps i), singletonREnv i (singletonRS {- (RATr (Ch next_i2 l') Strong)-} (ord l'))) | r' <- pderiv r l]
      }
    ; Nothing | l == l' -> do 
      { -- next_i <- incMaxId  
      ; return [ (ur, Eps i, singletonREnv i (singletonRS $ {- RNoCh (maximal rlvl Weak) -} case rlvl of { Weak -> 7000 ; _ -> 6000 })) ]
      }
              | l /= l' -> do 
      { -- next_i <- incMaxId
      ; next_i2 <- incMaxId
      ; return [ (ur, Eps i, singletonREnv i (singletonRS $ {- RATr (Ch next_i2 l') (maximal rlvl Weak) -} case rlvl of { Strong -> ord l' ; Weak -> 1000 + (ord l')}) ) ] 
      }
    }

urPDeriv (ur, (Any i)) l rlvl =   
  case lookup i ur of 
    { Just r -> 
         return [ ((updateUR i r' ur), (Eps i), singletonREnv i (singletonRS $ {- RNoCh Strong -} 6000) ) | r' <- pderiv r l ]
    ; Nothing -> return [ (ur, Eps i, singletonREnv i (singletonRS $ {- RNoCh (maximal rlvl Weak) -} case rlvl of { Strong -> 6000 ; Weak -> 7000 }) ) ]
    }
  
urPDeriv (ur, Pair i r1 r2) l rlvl =
   case lookup i ur of 
    { Just p -> 
        case pderiv p l of
          { [] -> return [] 
          ; ps  | posEmpty r1 -> do 
              { let ur2 =  ur `limit` fv r2 
              ; t1 <- urPDeriv (ur `limit` (fv r1), r1) l Strong 
              ; t2 <- urPDeriv (ur2, r2) l Strong
              ; t1 `seq` t2 `seq` return $ [ ((ur' ++ ur2 ++ [(i, Choice dontcare ps)]) , (Pair i r1' r2), renv) |  (ur', r1', renv) <- t1 ] ++ t2
              } 
                | otherwise   -> do 
              { let ur2 =  ur `limit` fv r2 
              ; t1 <- urPDeriv (ur `limit` (fv r1), r1) l Strong 
              ; t2 <- urPDeriv (ur2, r2) l Strong
              ; t1 `seq` t2 `seq` return $ [ ((ur' ++ ur2 ++ [(i, Choice dontcare ps)]) , (Pair i r1' r2), renv) |  (ur', r1', renv) <- t1] ++ [ (ur', r2', renv `combineREnv` renv') | (ur', r2', renv) <- t2, renv' <- mkFin r1 ]
              }
          }
    ; Nothing | posEmpty r1 -> do 
          { let ur2 =  ur `limit` fv r2 
          ; t1 <- urPDeriv (ur `limit` (fv r1), r1) l rlvl
          ; t2 <- urPDeriv (ur2, r2) l rlvl 
          ; t1 `seq` t2 `seq` return $ [ ((ur' ++ ur2) , (Pair i r1' r2), renv) |  (ur', r1', renv) <-  t1 ] ++ t2
          }
              | otherwise   -> do 
          { let ur2 =  ur `limit` fv r2
          ; t1 <- urPDeriv (ur `limit` (fv r1), r1) l rlvl
          ; t2 <- urPDeriv (ur2, r2) l rlvl 
          ; t1 `seq` t2 `seq` return $ [ ((ur' ++ ur `limit` (fv r2)) , (Pair i r1' r2), renv) |  (ur', r1', renv) <- t1 ] ++ [ (ur', r2', renv `combineREnv` renv') | (ur', r2', renv) <- t2, renv' <- mkFin r1 ]
          }
    }
urPDeriv (ur, Choice i rs) l rlvl = 
   case lookup i ur of
     { Just p ->  
         case pderiv p l of
         { [] -> return []
         ; ps -> do 
            { let ur' = updateUR i (Choice dontcare ps) ur
            ; ts <- mapM (\ r -> urPDeriv (ur', r) l Strong) rs
            ; ts `seq` return $ concat ts 
            -- todo:move i:is to each r
            }
         }
     ; Nothing -> do 
         { ts <- mapM (\ r -> urPDeriv (ur, r) l rlvl) rs
         ; ts `seq`  return $ concat ts
         }
     }
urPDeriv (ur, Star i r) l rlvl  = 
    case lookup i ur of 
      { Just p -> 
         case pderiv p l of
         { [] -> return []
         ; ps -> do 
            { let ur' = updateUR i (Choice dontcare ps) ur
            ; t <- urPDeriv (ur',r) l Strong
            ; t `seq` return [ (ur'', Pair i r' (Star i r), renv)  
                       | (ur'', r', renv) <- t ]
            }
         }
      ; Nothing -> do 
           { t <- urPDeriv (ur,r) l rlvl
           ; t `seq` return [ (ur', Pair i r' (Star i r), renv)  
                       | (ur', r', renv) <- t ]
           }
      }
urPDeriv ur c rlvl  = error $ "unhandled input: " ++ (show ur) ++ "/" ++ (show c)

-- make a non empty regex to accepts epsilon, structurally --todo shall we consider the ureq?
mkFin :: Re -> [REnv]
mkFin (Eps i)        = [emptyREnv]
mkFin (Ch i _)       = [singletonREnv i (singletonRS $ {- RMkFin Weak -} 5000 )]
mkFin (Any i)        = [singletonREnv i (singletonRS $ {- RMkFin Weak -} 5000 )]
mkFin (Pair i r1 r2) = [ renv1 `combineREnv` renv2 | renv1 <- mkFin r1, renv2 <- mkFin r2 ]
mkFin (Choice i rs)  = mkFin r1 ++ mkFin r2
mkFin (Star i r)     = [emptyREnv] 
mkFin _              = []


-- return all labels annotation of a re

fv :: Re -> [Int]
fv (Eps i) = [i]
fv (Ch i _) = [i]
fv (Any i)  = [i]
fv (Pair i r1 r2) = i:(fv r1 ++ fv r2)
fv (Choice i rs)  = i:(concatMap fv rs)
fv (Star i r) = i:(fv r)
fv _ = []


-- retrict the user req based on a set of labels

limit :: UReq -> [Int] -> UReq
limit ur is = filter (\(i,_) -> i `elem` is) ur



-- applying REnv to a Re


apply_ :: REnv -> Re -> Re 
apply_ renv r = let is = concatMap getLabels (resInREnv renv)
                    max_i = maximum $ (getLabels r) ++ is
                    io = logger "apply_ \n ============================================================================\n ============================================================================\n ============================================================================\n ============================================================================"
                in {- io `seq` -} run_ (Env max_i) (apply renv r)


-- note that for all (i,ROp) \in renv, i is a label to leaf node 

apply :: REnv -> Re -> State Env Re 
apply renv r = 
  let io = logger ("applying " ++ pretty r)
      (s,renv') = {- io `seq` -} simpl r renv 
      -- todo: this changes the renv' but it seems faster, not sure about correctness 
      -- more thoughts, maybe we shall split the simp into choice simplification and others non-choice simplification, because choice simplification is the only one that change the REnv.        
  in case s of
    { (Eps i) -> 
         case lookupREnv i renv' of 
           { Just rs -> do 
                { let trans = map (fromJust . reInROp) (Set.toList (atrs rs))
                      states = map (fromJust . reInROp) (asts rs)
                      eps  = if (mkfin rs) > 0 then True else False
                -- create a sequence concatenation out of the add-states ops
                ; ss' <- mkSeqS =<< mapM (apply renv') states
                -- create a choice out of the add transitions ops
                ; tt' <- mkChoiceS trans
                -- union the eps with ss' and tt'
                ; case (trans,states) of
                  { ([], [])    -> return s
                  ; ([], (_:_)) -> mkChoiceS [ss',s]
                  ; ((_:_),[] ) -> mkChoiceS [tt',s] 
                  ; (_,  _)     -> mkChoiceS [ss',tt',s]
                  }
                }
           ; Nothing -> return s        
           }
    ; (Ch i c) ->
           case lookupREnv i renv' of 
             { Just rs -> do 
                  { let trans = map (fromJust . reInROp) (Set.toList (atrs rs))
                        states = map (fromJust . reInROp) (asts rs)
                        eps  = if (mkfin rs) > 0 then True else False
                        -- create a sequence concatenation out of the add-states ops 
                  ; ss' <- mkSeqS =<< mapM (apply renv') states
                           -- append ss' to s
                  ; ss'' <- mkSeqS [s, ss']
                           -- create a choice out of the add transitions ops
                  ; tt' <- mkChoiceS trans
                           -- union tt' and eps with ss'' if there is mkFin, otherwise, just union tt' with ss''
                           
                  ; if eps 
                    then do 
                      { e <- mkEpsS 
                      ; case (trans,states) of
                        { ([], []) -> mkChoiceS [e, s]
                        ; ([], (_:_)) -> mkChoiceS [e,ss'']
                        ; ((_:_), []) -> mkChoiceS [e, tt',s] 
                        ; (_,  _)     -> mkChoiceS [e, tt',ss'']
                        }                           
                      }
                    else 
                      case (trans,states) of
                        { ([], []) -> return s 
                        ; ([], (_:_)) -> return ss''
                        ; ((_:_), []) -> mkChoiceS [tt',s] 
                        ; (_,  _)     -> mkChoiceS [tt',ss'']
                        } 
                  }
             ; Nothing -> return s        
             }
    ; (Any i) -> 
             case lookupREnv i renv' of 
               { Just rs -> do 
                    { let trans = map (fromJust . reInROp) (Set.toList (atrs rs))
                          states = map (fromJust . reInROp) (asts rs)
                          eps  = if (mkfin rs) > 0 then True else False
                    ; ss' <- mkSeqS =<< mapM (apply renv') states
                             -- append ss' to s
                    ; ss'' <- mkSeqS [s, ss']
                    ; case states of 
                      { [] | eps -> do  
                           { e <- mkEpsS 
                           ; mkChoiceS [e,s]
                           }
                           | otherwise -> return s
                      ; (_:_) | eps -> do 
                           { e <- mkEpsS 
                           ; mkChoiceS [e,ss'']
                           }
                              | otherwise -> return ss''
                      }
                    }
               ; Nothing -> return s
               }
    ; (Choice is rs) -> do 
             { rs' <- mapM (apply renv') rs
             ; return (Choice  is rs')
             }
    ; (Pair is r1 r2) -> do 
             { r1' <- apply renv' r1
             ; r2' <- apply renv' r2
             ; return (Pair is r1' r2')
             }
    ; (Star is r') -> do 
             { r'' <- apply renv' r'
             ; return (Star is r'')
             }
    ; others -> return s 
    }
             
mkSeqS :: [Re] -> State Env Re     
mkSeqS [] = return Phi 
mkSeqS (r:rs) = foldM (\a r -> do 
                          { i <- incMaxId 
                          ; return (Pair i a r)
                          }) r rs
                
mkChoiceS :: [Re] -> State Env Re                
mkChoiceS [] = do 
  { i <- incMaxId 
  ; return (Eps i)
  }
mkChoiceS [r] = return r
mkChoiceS (r:rs) = do 
  { i <- incMaxId
  ; return (Choice i (r:rs))
  }
     
mkEpsS :: State Env Re     
mkEpsS = do 
  { i <- incMaxId
  ; return (Eps i)
  }
      
{- 
apply :: REnv -> Re -> State Env Re 
apply renv' s = 
  let (r,renv) = simpl s renv' -- todo: this changes the renv' but it seems faster, not sure about correctness 
          -- more thoughts, maybe we shall split the simp into choice simplification and others non-choice simplification, because choice simplification is the only one that change the REnv.        
      -- r = simp s
      -- renv = renv'
  in case getLabel r of 
               {  (i:is) -> -- The first one is always the orginal label annotated to the regexp. The tail could contain those being collapsed because of pderiv op
                 case IM.lookup i renv of 
                   { Just rs -> do 
                         { r' <- apply' renv r
                         ; let adds = map (\ (RATr t _ ) -> t) $ filter isRATr rs
                               rs'  = filter isRASt rs
                         ; apps <- mapM (\ (RASt t _ ) -> apply renv t) rs'
                         ; let r''  = app r' apps 
                         ; case adds of 
                            { (_:_) -> do 
                              { next_i <- incMaxId 
                              ; return $ Choice (i:is) ((annotate [next_i] r''):adds)
                              }
                            ; [] -> return r'' }
                         }
                   ; Nothing -> apply' renv r
                   }
               ; [] -> error ("apply: getLabel is applied to a regular ex which has no label. " ++ (show r))
               }

apply' :: REnv -> Re -> State Env Re
apply' renv (Pair is r1 r2) = do { r1' <- apply renv r1 
                                 ; r2' <- apply renv r2 
                                 ; return $ Pair is r1' r2' }
apply' renv (Choice is rs) = do { rs' <- mapM (apply renv) rs
                                ; return $ Choice is rs' 
                                }
apply' renv (Star is r) = do { r' <- apply renv r
                             ; return $ Star is r' }
apply' _ r = return r

app :: Re -> [Re] -> Re
app r [] = r
app r (t:ts) = let is = getLabel r 
               in app (Pair is r (annotate is t)) ts
-}


{- not needed
extend :: REnv -> [Int] -> ROp -> REnv
extend renv [] _ = renv
extend renv (i:_) e@(RATr r lvl) = -- we only care about the original label
     case IM.lookup i renv of 
      { Just rs | not (e `elem` rs) ->  IM.adjust (\_ -> rs++[RATr r lvl]) i renv 
                | otherwise -> renv
      ; Nothing -> IM.insert i [RATr r lvl] renv
      }
-}


showL :: Show a => [a] -> IO ()
showL xs = do 
  { mapM_ (\x -> print x >> putStrLn "" ) xs }  



{- cheaper hack 
parse :: String -> Maybe Re
parse s = 
  case parsePat s of
    Left err -> Nothing 
    Right pat -> Just (patToRe pat)
    
    

patToRe :: Pat -> Re
patToRe (PVar i _ p) = 
  let r = patToRe p
  in r -- todo relabel r using i
patToRe (PPair p1 p2) = Pair dontcare (patToRe p1) (patToRe p2)
patToRe (PChoice p1 p2 _) = Choice dontcare [patToRe p1, patToRe p2]
patToRe (PStar p _) = Star dontcare (patToRe p)
patToRe (PE r) = reToRe r
patToRe p = error $ "patToRe: unhandle pattern " ++ (show p)
  
            
reToRe :: R.RE -> Re            
reToRe R.Empty = Eps dontcare
reToRe (R.L c) = Ch dontcare c
reToRe (R.Choice r1 r2 _) = Choice dontcare [reToRe r1, reToRe r2]
reToRe (R.Seq r1 r2) = Pair dontcare (reToRe r1) (reToRe r2)
reToRe (R.Star r _ ) = Star dontcare (reToRe r)
reToRe R.Any = Any dontcare
reToRe r = error $ "reToRe: unhandle pattern " ++ (show r)


-}


parse :: String -> Maybe Re
parse s = case parseEPat s of 
  { Left error -> Nothing
  ; Right (epat, estate) -> Just (rmSingletonChoice $ internalize epat)
  }
          

data TState = TState { ngi :: NGI
                     , gi :: GI
                     , anchorStart :: Bool
                     , anchorEnd :: Bool
                     }
          
type NGI = Int -- the non group index

type GI = Int -- the group index


initTState = TState { ngi = -3, gi = 1, anchorStart = False, anchorEnd = False } 


getNGI :: State TState NGI
getNGI = do { st <- get
            ; return $ ngi st
            }

getIncNGI :: State TState NGI -- get then increase
getIncNGI = do { st <- get
               ; let i = ngi st
               ; put st{ngi=(i-1)} 
               ; return i
               }

getGI :: State TState GI
getGI = do { st <- get
           ; return $ gi st
           }

getIncGI :: State TState GI -- get then increase 
getIncGI = do { st <- get
              ; let i = gi st
              ; put st{gi=(i+1)}
              ; return i
              }

getAnchorStart :: State TState Bool
getAnchorStart = do { st <- get
                    ; return (anchorStart st)
                    }

setAnchorStart :: State TState ()
setAnchorStart = do { st <- get
                    ; put st{anchorStart=True}
                    }

getAnchorEnd :: State TState Bool
getAnchorEnd  = do { st <- get
                   ; return (anchorEnd st)
                   }

setAnchorEnd :: State TState ()
setAnchorEnd = do { st <- get
                  ; put st{anchorEnd=True}
                  }


internalize :: EPat -> Re
internalize epat = case runState (intern epat) initTState of
  (re, state) -> re -- todo
  

intern :: EPat -> State TState Re
intern epat = p_intern epat
{-
  | hasGroup epat = p_intern epat
  | otherwise     = do 
    { r <- r_intern epat
    ; return r
    }
-}                    
p_intern :: EPat -> State TState Re
p_intern epat =            
  case epat of
    { EEmpty -> do
         { i <- getIncNGI
         ; return (Eps i) 
         }
    ; EGroup e -> do 
         { i <- getIncGI
         ; r <- intern e
         ; return (relabel i r)
         }
    ; EGroupNonMarking e -> intern e
    ; EOr es -> do
      { i <- getIncNGI
      ; rs <- mapM intern es
      ; return (Choice i rs)
      }
    ; EConcat es -> do 
      { rs <- mapM intern es
      ; case reverse rs of 
        { (r':rs') -> 
             foldM (\xs x -> do
                       { i <- getIncNGI
                       ; return (Pair i x xs) }) r' rs'
        ; [] -> error "an empty sequence encountered."
        }
      } 
    ; EOpt e _ -> do
      { i <- getIncNGI
      ; j <- getIncNGI
      ; r <- intern e
      ; return (Choice i [(Eps j), r])
      }
    ; EPlus e _ -> do 
      { i <- getIncNGI
      ; j <- getIncNGI
      ; r <- intern e
      ; r' <- intern e
      ; return (Pair i r (Star j r'))
      }
    ; EStar e _ -> do 
      { i <- getIncNGI
      ; r <- intern e
      ; return (Star i r)
      }
    ; EBound e low (Just high) _ -> do
      { r <- intern e
      ; let r1s = take low $ repeat r
      ; r1s' <- case r1s of 
        { [] -> do 
             { i <- getIncNGI
             ; return (Eps i)
             }
        ; (r1':r1s'') -> 
             foldM (\xs x -> do
                       { i <- getIncNGI
                       ; return (Pair i xs x)}) r1' r1s''
        }
      ; i <- getIncNGI
      ; let r2s = take (high - low) $ repeat (Choice i [r, Eps i])
      ; case r2s of  
        { [] -> do 
             { i <- getIncNGI
             ; return (Eps i)
             }
        ; (r2':r2s'') -> 
             foldM (\xs x -> do 
                       { i <- getIncNGI
                       ; return (Pair i xs x)}) r2' r2s''
        }
      ; case (r1,r2) of 
        { (Eps _, Eps _) -> return r1
        ; (Eps _, _ ) -> return r2
        ; (_, Eps _ ) -> return r1
        ; (_    , _ ) -> do 
          { i <- getIncNGI
          ; return (Pair i r1 r2) 
          }
        }
      }
    ; EBound e low Nothing _ -> do 
      { r <- intern e
      ; let r1s = take low $ repeat r
      ; r1s' <- case r1s of
        { (r1':r1s'') -> 
             foldM (\xs x -> do 
                       { i <- getIncNGI
                       ; return (Pair i xs x)}) r1' r1s''
        ; [] -> do 
          { i <- getIncNGI
          ; return (Eps i)
          }
        } 
      ; i <- getIncNGI
      ; j <- getIncNGI
      ; return (Pair i r1s' (Star j r))
      }
    ; ECarat -> do
      { notFirst <- getAnchorStart
      ; if notFirst
        then do 
          { i <- getIncNGI
          ; return (Ch i '^')
          }
        else do
          { setAnchorStart
          ; i <- getIncNGI
          ; return (Eps i)
          }
      }
    ; EDollar -> do 
      { f <- getAnchorEnd
      ; if f 
        then return ()
        else setAnchorEnd
      ; i <- getIncNGI
      ; return (Eps i)
      }
    ; EDot -> do 
      { i <- getIncNGI
      ; return (Any i)
      }
    ; EAny cs -> do 
      { i <- getIncNGI
      ; rs <- mapM (\x -> do 
                       { i <- getIncNGI
                       ; return (Ch i x) }) cs
      ; return (Choice i rs)
      }
    ; ENoneOf cs -> error "unable to handle NoneOf yet"
    ; EEscape c -> do 
      { i <- getIncNGI
      ; return (Ch i c)
      }
    ; EChar c -> do 
      { i <- getIncNGI
      ; return (Ch i c)
      }
    }
  

-- ^ relabel and taking the max src loc, this is to assume
-- either (i < 0  and j < 0)  or (either i > 0 or j > 0)
relabel :: SrcLoc -> Re -> Re
relabel i (Eps j) = Eps (max i j)
relabel i (Ch j c) = Ch (max i j) c
relabel i (Pair j r1 r2) = Pair (max i j) r1 r2
relabel i (Choice j rs) = Choice (max i j) rs
relabel i (Any j) = Any (max i j)
relabel i (Star j r) = Star (max i j) r

-- remove the singleton choice generated by the parser
-- 
rmSingletonChoice :: Re -> Re
rmSingletonChoice (Choice i [r]) = relabel i (rmSingletonChoice r)
rmSingletonChoice (Choice i rs)  = Choice i (map rmSingletonChoice rs)
rmSingletonChoice (Pair i r1 r2) = Pair i (rmSingletonChoice r1) (rmSingletonChoice r2)
rmSingletonChoice (Star i r) = Star i (rmSingletonChoice r)
rmSingletonChoice r = r
      
      
           
      
         
test :: UReq -> String -> S.ByteString -> Maybe String
test g pat_s word = 
  case parse pat_s of
    Nothing -> Nothing
    Just r  -> Just $ pretty $ (refine g r word) !! 0

                    
                    
  