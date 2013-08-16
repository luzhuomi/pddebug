> {-# LANGUAGE GADTs #-}

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




Regular expression debugging and reconstruction
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

where r is annotated with label at each AST level. $\Delta$ maps labels to sub-matches.


The mechanism
-------------

We use derivative (or partial derivative) operations to implement the word problem and the sub matching problem. See our recent papers (PPDP 12 )


The debugging algorithm
-----------------------

Refer to the PDDebug.lhs

The Refinement checking judgement
---------------------------------


> module Main where

> import System.Environment 
> import qualified Data.Map as M
> import qualified Data.IntMap as IM
> import System.IO.Unsafe
> import Data.List 
> import Data.Maybe
> import Data.Char


> import Control.Monad.ST
> import Data.STRef
> import Control.Monad
 

> logger mesg =  unsafePerformIO $ print mesg

 * The problem

Let  $\gamma$ denote the user specification, $w$ denote the input document , $r$ the pattern and  $r'$ the refined pattern, 
we use the judgement 
$$\gamma, r \vdash d : r'$$ 
to denote that under the user spec $\gamma$ , $r'$ is a replacement of $r$ that accepts $w$.

 * The user requirement 

\gamma ::= { (i, r) , ... , }
i ::= 1,2,3,...

> type UReq = [(Int, Re)]

> lookupUR :: Int -> UReq -> Maybe Re
> lookupUR i env = lookup i env

> updateUR :: Int -> Re -> UReq -> UReq
> updateUR x r ureq = map (\(y,t) -> if (x == y) then (y,r) else (y,t)) ureq

> allAccEps :: UReq -> Bool
> allAccEps ureq = all (\(x,t) -> posEmpty t) ureq

> inUR :: Int -> UReq -> Bool
> inUR i env = isJust (lookupUR i env) 

 * The Regular expression 
             
p ::= r^i 
r ::= () || (p|p) || pp || p* || l || \phi 
                          
> data Re where
>  Choice :: [Int] -> [Re] -> Re
>  Pair :: [Int] -> Re -> Re -> Re
>  Star :: [Int] -> Re -> Re
>  Ch :: [Int] -> Char -> Re
>  Eps :: [Int] -> Re
>  Phi :: Re
>  deriving (Show, Ord)


> instance Eq Re where
>     (==) (Choice _ rs1) (Choice _ rs2) = rs1 == rs2
>     (==) (Pair _ r1 r2) (Pair _ r1' r2') = r1 == r1' && r2 == r2'
>     (==) (Star _ r1) (Star _ r2) = r1 == r2
>     (==) (Ch _ c1) (Ch _ c2) = c1 == c2
>     (==) Eps{} Eps{} = True
>     (==) Phi Phi = True
>     (==) _ _ = False



> posEmpty :: Re -> Bool
> posEmpty (Eps _)        = True
> posEmpty (Choice _ rs)  = any posEmpty rs
> posEmpty (Pair _ r1 r2) = posEmpty r1 && posEmpty r2
> posEmpty (Star _ _)     = True
> posEmpty (Ch _ _)       = False
> posEmpty Phi            = False

> isPhi :: Re -> Bool 
> isPhi Phi            = True
> isPhi (Ch _ _ )      = False
> isPhi (Choice _ rs)  = all isPhi rs
> isPhi (Pair _ r1 r2) = isPhi r1 || isPhi r2 
> isPhi (Star _ _)     = False
> isPhi (Eps _)        = False

> isChoice :: Re -> Bool
> isChoice Choice{} = True
> isChoice _ = False


containment check

> contain :: Re -> Re -> Bool
> contain r1 r2 = containBy M.empty r2 r1

> data Leq = Leq Re Re deriving (Eq, Ord, Show)

> containBy :: M.Map Leq () -> Re -> Re -> Bool
> containBy env Phi _ = True
> containBy env r1 r2 = 
>   case M.lookup (Leq r1 r2) env of   
>    { Just _  -> True  
>    ; Nothing | posEmpty r1 && not (posEmpty r2) -> False
>              | otherwise -> let env' = M.insert (Leq r1 r2)  () env
>                             in  all (\l -> containBy env' (deriv r1 l) (deriv r2 l)) (sigma (Choice dontcare [r1,r2]))
>    }
> deriv r l = Choice dontcare (pderiv r l)

> equiv :: Re -> Re -> Bool
> equiv r1 r2 = r1 `contain` r2 && r2 `contain` r1


simplification 

> collapse x y = nub (sort (x ++ y))
> combine x y = nub (sort (x ++ y))

> shift :: [Int] -> Re -> Re 
> shift ls Phi = Phi
> shift ls (Choice ls' rs) = Choice (combine ls' ls) rs
> shift ls (Ch ls' c) = Ch (combine ls' ls) c
> shift ls (Pair ls' r1 r2) = Pair (combine ls' ls) r1 r2
> shift ls (Star ls' r) = Star (combine ls' ls) r
> shift ls (Eps ls') = Eps (combine ls' ls)


> simp :: Re -> Re
> simp (Pair l1 (Eps l2) r) 
>   | isPhi r   = Phi
>   | otherwise = r -- shift (collapse l1 l2) r -- this will destroy the original structure labels
> simp (Pair l r1 r2)
>   | isPhi r1 || isPhi r2 = Phi
>   | otherwise            = Pair l (simp r1) (simp r2)
> simp (Choice l []) = Eps l
> simp (Choice l [r]) = shift l r
> {- simp (Choice l rs)  -- this will destroy the structure
>  | any isChoice rs =  
>     Choice l $ 
>        foldl (\rs-> \r-> case r of
>                Choice l rs2 -> rs ++ (map (shift l) rs2)
>                _            -> rs ++ [r])
>              [] rs 
>  | otherwise = Choice l $ nub $ filter (not.isPhi) $ map simp rs -}
> simp (Choice l rs) = Choice l $ nub $ filter (not.isPhi) $ map simp rs
> simp (Star l1 (Eps l2)) = Eps $ collapse l1 l2 
> simp (Star l1 (Star l2 r)) = Star (combine l1 l2) r 
> simp (Star l r)
>  | isPhi r   = Eps l
>  | otherwise = Star l $ simp r 
> simp x = x 



> class PDeriv t where
>   pderiv :: t -> Char -> [Re]


partial derivatives of regex

> instance PDeriv Re where
>   pderiv (Eps _) _ = []
>   pderiv (Choice x rs) l = nub $ concatMap (\r -> pderiv r l) rs -- x?
>   pderiv (Pair x r1 r2) l | posEmpty r1 = nub [ Pair x r1' r2 | r1' <- pderiv r1 l] ++ (pderiv r2 l)
>                           | otherwise =  [ Pair x r1' r2 | r1' <- pderiv r1 l]
>   pderiv (Star x r) l = [ Pair x r' (Star x r) | r' <- pderiv r l ]
>   pderiv (Ch x c) l | c == l = [ Eps x ]
>                     | otherwise = []
>   pderiv Phi _ = []

* partial derivatives of a set of regexs

> instance PDeriv t => PDeriv [t] where
>   pderiv rs l = concatMap (\r -> pderiv r l) rs

* partial dervatives extended to user-requirement-regex pair

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




partial derivative
  
  

> class Accept t where
>   accept :: t -> Doc -> Bool

> instance Accept Re where
>   accept r ls = any posEmpty $ foldl (\rs l -> pderiv r l) [r] ls 

> instance Accept t => Accept [t] where
>   accept rs ls = any (\r -> accept r ls) rs

> type Doc = [Char]

> getLabels :: Re -> [Int]
> getLabels (Eps x)      = x
> getLabels (Choice x rs) =  x ++ concatMap getLabels rs
> getLabels (Pair x r1 r2) = x ++ (getLabels r1) ++ (getLabels r2)
> getLabels (Star x r)   = x ++ (getLabels r)
> getLabels (Ch x _)     = x
> getLabels Phi          = []



> getLabel :: Re -> [Int]
> getLabel (Eps x)      = x
> getLabel (Choice x _) = x
> getLabel (Pair x _ _) = x
> getLabel (Star x _)   = x
> getLabel (Ch x _)     = x
> getLabel Phi          = []

> dontcare = []


> annotate :: [Int] -> Re -> Re
> annotate is (Eps _) = Eps is
> annotate is (Choice x cs) = Choice is cs
> annotate is (Pair x r1 r2) = Pair is r1 r2
> annotate is (Star x r) = Star is r
> annotate is (Ch x c) = Ch is c
> annotate is Phi = Phi


> sigma :: Re -> String
> sigma (Choice _ rs) = nub $ concat $ map sigma rs
> sigma (Pair _ r1 r2) = nub $ (sigma r1) ++ (sigma r2)
> sigma (Star _ r) = sigma r
> sigma (Ch _ c) = [c]
> sigma Eps{} = []
> sigma Phi = []


* The Replacement Relation 
We use the following judgement to denote the replacement relation
$$ \gamma, p \turns d : q $$ 
where $\gamma$ is the user requirement, $p$ is the existing regular expression, $w$ is the input document and $q$ is the replacement regular expression.
It reads, under user requirement $\gamma$, $p$ can be replaced by $q$ which accepts $w$. 

There are two properties follows 

 1. $d\in r \Longrightarrow \Delta$ implies $ \Delta \vdash \gamma$ and $r \subseq t$.
 2. $d \not \in r$ implies $r \gamma\over\approximate t$  and $d \in t \Longrightarrow \Delta$ and $\Delta \vdash \gamma$.

The first property ensures that the replacement is subsuming the orginal regex $r$ if $w$ is already in $r$ and the matching result is conforming to the user requirement.
The second property ensures that if $w$ is not in $r$, the replacement shall have the same requirement-shape as the orginal one and conform to the user requirement. 


> replacement :: UReq -> Re -> Doc -> Re -> Bool 

  i \in dom(\gamma) 
  d \in \gamma(i) 
  \gamma - {i}, r \vdash d, r'                           
 ----------------------------- (pExist)
  \gamma, r^i \vdash d : r'^i

> replacement ureq r w r' = 
>    let ls = getLabels r  
>        ls'  = getLabels r'          
>    in ls == ls' && 
>      ( undefined
>      )


   i \not \in dom(\gamma)
   \gamma - {i}, r \vdash d : r'
 ------------------------------- (pIgnore)
 \gamma, r^i \vdash d : r'^i


   d \in r
 ------------------------- (rEmp)
 \gamma, () \vdash d : r

   d \in r 
 ------------------------- (rLab)
 \gamma, l \vdash d : r



  fv(r1) = \bar{i1} fv(r2 = \bar{i2} 
 \gamma_{\bar{i1}}, r1 \vdash d1 : r1'                              
 \gamma_{\bar{i2}}, r2 \vdash d2 : r2'                         
 ------------------------------------- (rSeq)
 \gamma, r1r2 \vdash d1d2 : r1'r2'

 we use \gamma_{\bar{i}} to denote { (i,\gamma(i)) | i \in \bar{i} and i \in dom(\gamma) }
                          
                          
  \gamma, r1 \vdash d : r1'
 -------------------------------------- ( rOr1)   
 \gamma, r1|r2 \vdash d : r1'|r2                          


  \gamma, r2 \vdash d : r2'
 -------------------------------------- ( rOr2)   
 \gamma, r1|r2 \vdash d : r1|r2'                          


  \gamma, r \vdash di : r'  \forall i \in {1,n}
 ------------------------------------------------- ( rStar)   
 \gamma, r* \vdash d1...dn : r'*                          


Rules rSeq, rOr1, rOr2 and rStar validate the replacement relation indeterministically



  \gamma,p \vdash d:p'    \forall d\in D 
 ---------------------------------------- (pDocS)
  \gamma p \vdash D : p'






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


                          
r1 = (A|B)*

> r1 = Star [1] (Choice [2] [Ch [3] 'A', Ch [4] 'B'])

r2 = (A|B|C)*

> r2 = Star [1] (Choice [2] [Ch [3] 'A'])


> r3 = Pair [1] (Ch [2] 'A') (Ch [3] 'B')

r4 = ()

> r4 = Eps [1] 

t3 = .+

> t3 = Pair dontcare (Choice dontcare [Ch dontcare 'A',Ch dontcare 'B',Ch dontcare 'C']) (Star dontcare (Choice dontcare [Ch dontcare 'A',Ch dontcare 'B',Ch dontcare 'C']))

> t4 = Pair dontcare (Choice dontcare [Ch dontcare 'A',Ch dontcare 'B']) (Star dontcare (Choice dontcare [Ch dontcare 'A',Ch dontcare 'B']))


> v = "ABC"

> g1 = [(1::Int, t3)]

> g2 = [(1::Int, t4)]


w = <h><d>65103020</d></h>
r5 = .*<s>([0-9]+)</s>.*
g5 = [(1::Int, [0-9]+)]


> -- anySym x = Choice [x] (map (\i -> (Ch [(100*x+i)] (chr i))) ([47,60,62] ++ [100,104])) 

> anySym x = Choice [x] (map (\i -> (Ch [(100*x+i)] (chr i))) [0..128]) -- this will take super long time

> anyNum x = Choice [x] (map (\i -> (Ch [(100*x+i)] (chr i))) [48]) 

> w = "<h><d>0000</d></h>"
> r5 = Pair [1] p1 (Pair [2] p2 (Pair [3] p3 (Pair [4] p4 p5)))
>   where p1 = Star [20] (anySym 30) 
>         p2 = Pair [41] (Ch [42] '<') (Pair [43] (Ch [44] 's') (Ch [45] '>'))
>         p3 = Star [50] (anyNum 51)
>         p4 = Pair [61] (Ch [62] '<') (Pair [63] (Ch [64] '/') (Pair [65] (Ch [66] 's') (Ch [67] '>')))
>         p5 = Star [70] (anySym 80)
> g5 = [(50::Int, Pair [] (anyNum 90) (Star [] (anyNum 90)))]



w1 = (A)
r6 = <(A|B)*>

> w1 = "(A)"
> r6 = Pair [0] 
>       (Ch [1] '<') 
>       (Pair [2] (Star [3] (Choice [4] [(Ch [5] 'A'),(Ch [6] 'B')]))
>           (Ch [7] '>'))
> g6 = [(3::Int, r1)]



w2 = (A)
r7 = .*<(A|B)*>.*

there are still some space for pruning
sortBy (\x y -> compareREnv (snd x) (snd y) )  (ref' [(g7,r7, IM.empty)] "(A)") !! 0
sortBy (\x y -> compareREnv (snd x) (snd y) )  (ref' [(g7,r7, IM.empty)] "(A)") !! 1
sortBy (\x y -> compareREnv (snd x) (snd y) )  (ref' [(g7,r7, IM.empty)] "(A)") !! 2
sortBy (\x y -> compareREnv (snd x) (snd y) )  (ref' [(g7,r7, IM.empty)] "(A)") !! 3
sortBy (\x y -> compareREnv (snd x) (snd y) )  (ref' [(g7,r7, IM.empty)] "(A)") !! 4

> w2 = "(A)"
> r7 = Pair [-10]
>       (Star [-20] (Choice [-21] [Ch [-22] 'A', Ch [-23] 'B', Ch [-24] '<', Ch [-25] '>']))
>       (Pair [-30] 
>        (Pair [0] 
>         (Ch [1] '<') 
>         (Pair [2] (Star [3] (Choice [4] [(Ch [5] 'A'),(Ch [6] 'B')]))
>           (Ch [7] '>')))
>        (Star [-40] (Choice [-41] [Ch [-42] 'A', Ch [-43] 'B', Ch [-44] '<', Ch [-45] '>']))
>       )
> g7 = [(3::Int, r1)]


> hasStrong :: REnv -> Bool
> hasStrong renv = let rops = concatMap snd (IM.toList renv)
>                  in any isStrong rops


> main :: IO ()
> main = do 
>   [si] <- getArgs
>   let i = read si
>   print $ (refine g5 r5 w) !! i


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


> type REnv = IM.IntMap [ROp]

> data ROp = RATr Re RLevel  -- add transition
>          | RASt Re RLevel  -- add state
>          | RNoCh RLevel     -- no change
>           deriving (Eq,Show)

> reInROp :: ROp -> Maybe Re
> reInROp (RATr r _) = Just r
> reInROp (RASt r _) = Just r
> reInROp (RNoCh _) = Nothing

> resInROps :: [ROp] -> [Re]
> resInROps [] = []
> resInROps ((RATr r _):rops) = r:(resInROps rops)
> resInROps ((RASt r _):rops) = r:(resInROps rops)
> resInROps ((RNoCh  _):rops) = resInROps rops


> resInREnv :: REnv -> [Re]
> resInREnv renv = 
>   resInROps $ concat $ map snd (IM.toList renv)

        


> compareREnv :: REnv -> REnv -> Ordering
> compareREnv r2 r1 = 
>   let sTr1 = countStrongATr r1  
>       sTr2 = countStrongATr r2
>       sSt1 = countStrongASt r1
>       sSt2 = countStrongASt r2
>       sNC1 = countStrongNoCh r1
>       sNC2 = countStrongNoCh r2

>       wTr1 = countWeakATr r1  
>       wTr2 = countWeakATr r2
>       wSt1 = countWeakASt r1
>       wSt2 = countWeakASt r2
>       wNC1 = countWeakNoCh r1
>       wNC2 = countWeakNoCh r2

>   in case compare sNC1 sNC2 of 
>      { EQ -> case compare sTr1 sTr2 of
>         { EQ -> case compare sSt1 sSt2 of
>           { EQ -> case compare wNC1 wNC2 of
>             { EQ -> compare wTr1 wTr2
>             ; others -> others }  
>           ; others -> others }
>         ; others -> others }
>      ; others  -> others }


count the number of ROps in renv

> renvSize :: REnv -> Int
> renvSize renv = sum (map (\ (k,v) -> length v) (IM.toList renv))

> renvStrong :: REnv -> Int
> renvStrong renv = sum (map (\ (k,v) -> length (filter isStrong v)) (IM.toList renv))

> renvWeak :: REnv -> Int
> renvWeak renv = sum (map (\ (k,v) -> length (filter isWeak v)) (IM.toList renv))

> renvRASt :: REnv -> Int
> renvRASt renv = sum (map (\ (k,v) -> length (filter isRASt v)) (IM.toList renv))

> countStrongATr :: REnv -> Int 
> countStrongATr renv = sum (map (\ (k,v) -> length (filter (\x -> (isStrong x) && (isRATr x)) v)) (IM.toList renv))

> countStrongASt :: REnv -> Int 
> countStrongASt renv = sum (map (\ (k,v) -> length (filter (\x -> (isStrong x) && (isRASt x)) v)) (IM.toList renv))

> countStrongNoCh :: REnv -> Int 
> countStrongNoCh renv = sum (map (\ (k,v) -> length (filter (\x -> (isStrong x) && (isRNoCh x)) v)) (IM.toList renv))


> countWeakATr :: REnv -> Int 
> countWeakATr renv = sum (map (\ (k,v) -> length (filter (\x -> (isWeak x) && (isRATr x)) v)) (IM.toList renv))

> countWeakASt :: REnv -> Int 
> countWeakASt renv = sum (map (\ (k,v) -> length (filter (\x -> (isWeak x) && (isRASt x)) v)) (IM.toList renv))

> countWeakNoCh :: REnv -> Int 
> countWeakNoCh renv = sum (map (\ (k,v) -> length (filter (\x -> (isWeak x) && (isRNoCh x)) v)) (IM.toList renv))

                         
                         
> isStrong :: ROp -> Bool
> isStrong (RATr _ Strong) = True                         
> isStrong (RATr _ _) = False
> isStrong (RASt _ Strong) = True                         
> isStrong (RASt _ _) = False
> isStrong (RNoCh Strong) = True                         
> isStrong (RNoCh _) = False

> isWeak :: ROp -> Bool
> isWeak (RATr _ Weak) = True                         
> isWeak (RATr _ _) = False
> isWeak (RASt _ Weak) = True                         
> isWeak (RASt _ _) = False
> isWeak (RNoCh Weak) = True                         
> isWeak (RNoCh _) = False

> isRATr :: ROp -> Bool
> isRATr (RATr _ _) = True
> isRATr _ = False

> isRASt :: ROp -> Bool
> isRASt (RASt _ _) = True
> isRASt _ = False

> isRNoCh :: ROp -> Bool
> isRNoCh (RNoCh _) = True
> isRNoCh _ = False
                       
                       
> data RLevel = Strong | Weak deriving (Ord, Eq, Show)


renv_1 \entails renv_2 iff 
   \forall l in renv_2 s.t. renv_1(l) superseteq renv_2(l) 
  
 note the equality among ROp we ignore the loc of the Re

> entail :: REnv -> REnv -> Bool 
> entail r1 r2 = 
>   let ks = IM.keys r2
>   in all (\k -> case (IM.lookup k r1, IM.lookup k r2) of
>             { (Just rs1, Just rs2) -> rs1 `ropSubsume` rs2
>             ; (_,_) -> False } ) ks

> ropSubsume :: [ROp] -> [ROp] -> Bool
> ropSubsume rs1 rs2 = all (\r2 -> r2 `elem` rs1) rs2



top level function

> refine :: UReq -> Re -> [Char] -> [Re]
> refine ureq r cs = 
>   let renvs = nub $ sortBy compareREnv (ref [(ureq, r, IM.empty)] cs)
>   in  map (\renv ->  apply_ renv r)  renvs

the main routine

> ref :: [(UReq, Re, REnv)] -> [Char] -> [REnv]
> ref urs [] = [ renv | (ureq, r, renv) <- urs, posEmpty (renv `apply_` r) ] ++ 
>              [ extend renv (getLabel r) (RATr (Eps dontcare) Strong) -- try to fix those states which are non-final?
>                     | (ureq, r, renv) <- urs
>                     , not (posEmpty (renv `apply_` r))
>                     , any (\i -> case lookupUR i ureq of
>                                  { Nothing -> False
>                                  ; Just t  -> posEmpty t }) (getLabel r) ]
> ref urs (l:w) = let 
>                     urs' = concatMap (\ (ur,r,renv) -> 
>                                     let urs'' = urePDeriv (ur, r, renv) l
>                                     in  prune3 r $ map (\(ur', r', renv') -> (ur', r',  combineEnv renv renv')) urs'') urs
>                 in ref urs' w




> ref' :: [(UReq, Re, REnv)] -> [Char] -> [(Re,REnv)]
> ref' urs [] = [ (r,renv) | (ureq, r, renv) <- urs ] 
> ref' urs (l:w) = let 
>                      urs' = concatMap (\ (ur,r,renv) -> 
>                                     let urs'' = urePDeriv (ur, r, renv) l
>                                     in  prune3 r $ prune4 $ map (\(ur', r', renv') -> 
>                                                    let io = logger $ ("combining " ++ show renv ++ " with " ++ show renv' ++ " yielding " ++ (show $ combineEnv renv renv')  )
>                                                    in  (ur', r',  combineEnv renv renv')) urs'') urs
>                  in ref' urs' w

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


> prune :: [(UReq, Re, REnv)] -> [(UReq, Re, REnv)]
> prune ts = let sts = sortBy (\(_,_,r1) (_,_,r2) -> compare (renvSize r2) (renvSize r1)) ts
>            in prune' sts


> prune' :: [(UReq, Re, REnv)] -> [(UReq, Re, REnv)]
> prune' [] = []
> prune' (x:xs) | any (\y -> (trd x) `entail` (trd y)) xs = prune' xs
>               | otherwise = (x:(prune' xs))

> trd :: (a,b,c) -> c
> trd (_,_,x) = x




prune by semantic equivalent 


> prune2 :: Re -> [(UReq, Re, REnv)] -> [(UReq, Re, REnv)]
> prune2 r [] = []
> prune2 r (x:xs) | any (\y -> containGTE r x y) xs = prune2 r xs
>                 | otherwise = x:(prune2 r xs)
>   where containGTE r x y = let ex = trd x 
>                                ey = trd y                                
>                            in (apply_ ex r) `equiv` (apply_ ey r) && (compareREnv ex ey >= EQ) 



prune by isomorphism.

Let r be a regular expression, (l1, rops1) and (l2, rops2) Label-ROp pairs, they are considered iso w.r.t to r iff
   1) l1 == l2 and rops1 == rops2 or
   2) l1 and l2 are labels of the two alternatives of the choice sub-exp in r

e.g. r = (Choice [1] (Ch [2] 'A') (Ch [3] 'B'))

 (2, ATr (Ch [4] 'C')) and (3, ATr (Ch [5] 'C')) are considered iso w.r.t to r.

Rationale: applying the above two operations lead to the semantically equivalent regex

> prune3 :: Re -> [(UReq, Re, REnv)] -> [(UReq, Re, REnv)]
> prune3 r [] = [] 
> prune3 r (x:xs) | any (\y -> iso r (trd x) (trd y)) xs = prune3 r xs
>                 | otherwise = x:(prune3 r xs)
>   where iso r renv_x renv_y 
>           | (IM.size renv_x /= IM.size renv_y) = False
>           | otherwise =  
>               let ps1 = IM.toList renv_x
>                   ps2 = IM.toList renv_y
>               in isoPairs r ps1 ps2
>         isoPairs r [] [] = True
>         isoPairs r _  [] = False
>         isoPairs r [] _  = False
>         isoPairs r ((lx,x):xs) ((ly,y):ys)  -- assumption, IM.toList sort by the keys
>            | lx == ly  = (x == y) && (isoPairs r xs ys)
>            | choiceAlts r lx ly = (x == y) && (isoPairs r xs ys)
>            | otherwise = False


> prune4 :: [(UReq, Re, REnv)] -> [(UReq, Re, REnv)]
> prune4 [] = []
> prune4 ((x@(_,_,renv)):xs) | hasDupROps renv = prune4 xs
>                            | otherwise = x:(prune4 xs)

> hasDupROps :: REnv -> Bool 
> hasDupROps renv = let ps = IM.toList renv 
>                   in any (\(k,rops) -> 
>                       let rops' = filter (not . isRNoCh) rops in length (nub rops') /= length rops') ps

check whether the two labels are siblings under the choice sub-exp in r

> choiceAlts :: Re -> Int -> Int -> Bool 
> choiceAlts (Choice _ rs) x y = 
>      let ls = concatMap getLabels rs  
>      in x `elem` ls && y `elem` ls
> choiceAlts (Pair _ r1 r2) x y = choiceAlts r1 x y || choiceAlts r2 x y
> choiceAlts (Star _ r) x y  = choiceAlts r x y 
> choiceAlts (Ch _ _) _ _ = False
> choiceAlts (Eps _ ) _ _ = False
> choiceAlts Phi      _ _ = False


> urePDeriv :: (UReq, Re, REnv) -> Char -> [(UReq, Re, REnv)]
> urePDeriv (ur, r, psi) l = -- pre-cond: psi has been applied to r. No, some of the labels DO NOT appear in r, because r is just a partial derivatives!
>   let max_i = maximum $ (getLabels r) ++ (concatMap getLabels $ resInREnv psi)
>       (t,e) = run (Env max_i) (urPDeriv (ur, r) l Weak)
>   in [ (ur', r''', psi'') | (ur', r', psi') <- t,  -- let r''' = r', let psi'' = psi' ] 
>                             let r'' = run_ e (psi' `apply` r'),  -- we can only apply simplification after we apply psi' to r' 
>                             let io = logger ("simpl " ++ show r'' ++ " with " ++ show psi'),
>                             let (r''',psi'') = {- io `seq` -} simpl  r'' psi' ,
>                             not (isRedundant psi r psi'' r''' ) ] -- e.g. adding 'a' to (a|b), since there already an 'a' -- can't just check whether r \equiv r''' , because there are RNoCh rops


> isRedundant :: REnv -> Re -> REnv -> Re -> Bool 
> isRedundant renv1 r1 renv2 r2 = 
>   let diff = diffREnv renv2 renv1
>   in -- (not (all isRNoCh diff)) && (r1 `equiv` r2) 
>      -- checking for (r1 `equiv` r2) is expensive
>      (any (\(k, rops) -> any (not . isRNoCh) rops) (IM.toList diff)) && bogusDiff diff r1
>    where bogusDiff diff (Choice (l:_) rs) = 
>            case IM.lookup l diff of              
>             { Just rops -> any (\(RATr r _) -> r `elem` rs) rops
>             ; Nothing -> False }  
>          bogusDiff diff (Pair _ r1 r2) = bogusDiff diff r1 || bogusDiff diff r2
>          bogusDiff diff (Star _ r) = bogusDiff diff r
>          bogusDiff diff (Ch _ _) = False
>          bogusDiff diff (Eps _) = False
>          bogusDiff diff Phi = False

> diffREnv :: REnv -> REnv -> REnv -- rops in r2 but not in r1
> diffREnv r2 r1 = 
>  let ps = IM.toList r2  
>      ps' = foldl (\acc (k,rops) -> case IM.lookup k r1 of
>       { Nothing -> acc ++ [(k,rops)]
>       ; Just rops' -> acc ++ [(k,filter (\rop -> not (rop `elem` rops')) rops)] } ) [] ps
>  in IM.fromList ps'


*Main> showL (map id $ sortBy (\x y -> compareREnv (snd x) (snd y) )  (ref' [(g1,r1, IM.empty)] "CC") )
(Star [1] (Choice [2] [Ch [3] 'A',Ch [4,7] 'B',Ch [4,6] 'C']),fromList [(2,[RATr (Ch [6] 'C') Strong]),(4,[RNoCh Strong])])

(Star [1] (Choice [2] [Ch [3] 'A',Ch [4,7,10] 'B',Ch [4,7,9] 'C',Ch [4,6,11] 'C',Ch [4,6,9] 'C']),fromList [(2,[RATr (Ch [6] 'C') Strong])])


vs

(Star [1] (Choice [2] [Ch [3] 'A',Choice [4] [Ch [7] 'B',Ch [6] 'C']]),fromList [(4,[RATr (Ch [6] 'C') Strong]),(6,[RNoCh Strong])])

(Star [1] (Choice [2] [Ch [3] 'A',Choice [4] [Choice [7] [Ch [10] 'B',Ch [9] 'C'],Ch [6] 'C']]),fromList [(4,[RATr (Ch [6] 'C') Strong]),(7,[RATr (Ch [9] 'C') Strong])])


> simpl :: Re -> REnv -> (Re, REnv)
> simpl (Pair l1 (Eps l2) r) renv 
>   | isPhi r  = (Phi,renv)
>   | otherwise = (r,renv) -- todo:check
> simpl (Pair l r1 r2) renv 
>   | isPhi r1 || isPhi r2 = (Phi,renv)
>   | otherwise            = let (r1', renv') = simpl r1 renv
>                                (r2', renv'') = simpl r2 renv'                               
>                            in (Pair l r1' r2', renv'')
> simpl (Choice l []) renv = (Eps l, renv)
> simpl (Choice l [r]) renv = (shift l r, renv) -- todo: check
> simpl (Choice l rs) renv 
>   | any isChoice rs = 
>      let (rs',e') = foldl (\(rs,e) -> \r -> case r of
>                     { Choice l' rs2 -> ((rs ++ (map {- (shift l')-} id  rs2)), reloc l' l e)
>                     ; _             -> (rs ++ [r], e) }) ([],renv) rs 
>      in (Choice l rs', e')
>  | otherwise = 
>      let (rs',e'') = foldl (\(rs,e) -> \r-> 
>                        let (r',e') = simpl r e                 
>                        in if isPhi r'
>                           then (rs,e')
>                           else (rs++[r],e')                                   
>                      ) ([],renv) rs -- todo: check for duplicate
>      in (Choice l rs', e'')
> simpl (Star l1 (Eps l2)) renv = (Eps (collapse l1 l2), renv) --todo:
> simpl (Star l1 (Star l2 r)) renv = (Star (combine l1 l2) r, renv)
> simpl (Star l r) renv
>  | isPhi r   = (Eps l, renv)
>  | otherwise = let (r',e) = simpl r renv in (Star l r',e)
> simpl x e = (x,e)

reloc : relocate rop under l' to l in a renv

> reloc :: [Int] -> [Int] -> REnv -> REnv
> reloc ls' [] renv = renv -- error?
> reloc ls' ls@(l:_) renv = let io = logger ("relocating " ++ show ls' ++ " to " ++ show ls)
>   in {- io `seq` -} foldl (\e l' -> relocSingle l' l e) renv ls'
> relocSingle :: Int -> Int -> REnv -> REnv
> relocSingle l' l renv  =
>    case IM.lookup l' renv of
>    { Just rops' -> IM.delete l' $ case IM.lookup l renv of 
>                    { Nothing -> IM.insert l rops' renv
>                    ; Just rops -> IM.update (\_ -> Just (rops++rops')) l renv
>                    }
>    ; Nothing    -> renv
>    }



finding the maximal among two RLevels

> maximal :: RLevel -> RLevel -> RLevel
> maximal Strong _ = Strong
> maximal _ Strong = Strong
> maximal _ _ = Weak

> newtype State s a = State { runState :: (s -> (a,s)) } 
 
> instance Monad (State s) where
>   return a        = State (\s -> (a,s))
>   (State x) >>= f = State (\s -> let (a,s') = x s 
>                                      stb = f a
>                                  in (runState stb) s')

> run :: s -> State s a -> (a,s)
> run s sta = (runState sta) s


> run_ :: s -> State s a -> a
> run_ s sta = fst $ run s sta

> data Env = Env { maxId :: Int
>                } deriving Show

> setMaxId :: Int -> State Env ()
> setMaxId i = State (\env -> let env' = env{maxId = i}
>                             in ((), env'))


> getMaxId :: State Env Int
> getMaxId = State (\env -> (maxId env,env))

> incMaxId :: State Env Int
> incMaxId = do 
>  { max_i <- getMaxId 
>  ; let next_i = max_i + 1
>  ; setMaxId next_i                    
>  ; return next_i 
>  }


> urPDeriv :: (UReq, Re) -> Char -> RLevel -> State Env [(UReq, Re, REnv)]
> urPDeriv (ur, Eps (i:is)) l rlvl
>   | i `inUR` ur = do 
>      { next_i <- incMaxId
>        -- let next_i  = i  
>      ; return [ ((updateUR i r' ur), Eps [next_i], IM.singleton i [RASt (Ch [next_i] l) Strong]) 
>                      | let r = fromJust (lookupUR i ur), r' <- pderiv r l ] 
>      }
>   | otherwise   = do 
>      { next_i <- incMaxId 
>        -- let next_i  = i    
>      ; return [ (ur, Eps [next_i], IM.singleton i [RASt (Ch [next_i] l) (maximal rlvl Weak)]) ]
>      }
> urPDeriv (ur, (Ch (i:is) l)) l' rlvl = 
>   case lookup i ur of 
>     { Just r | l == l' -> do 
>       { -- next_i <- incMaxId
>       ; return  [ ((updateUR i r' ur), (Eps (i:is)), IM.singleton i [RNoCh Strong] )
>                          | r' <- pderiv r l ]
>       }
>              | l /= l' -> do 
>       { -- next_i <- incMaxId
>       ; next_i2 <- incMaxId
>       ; return  [ ((updateUR i r' ur), (Eps (i:is)), IM.singleton i [RATr (Ch [next_i2] l') Strong]) | r' <- pderiv r l]
>       }
>     ; Nothing | l == l' -> do 
>       { -- next_i <- incMaxId  
>       ; return [ (ur, Eps (i:is), IM.singleton i [RNoCh (maximal rlvl Weak)] ) ]
>       }
>               | l /= l' -> do 
>       { -- next_i <- incMaxId
>       ; next_i2 <- incMaxId
>       ; return [ (ur, Eps (i:is), IM.singleton i [RATr (Ch [next_i2] l') (maximal rlvl Weak)] ) ] 
>       }
>     }
> urPDeriv (ur, Pair (i:is) r1 r2) l rlvl =
>    case lookup i ur of 
>     { Just p -> 
>         case pderiv p l of
>           { [] -> return [] 
>           ; ps  | posEmpty r1 -> do 
>               { let ur2 =  ur `limit` fv r2 
>               ; t1 <- urPDeriv (ur `limit` (fv r1), r1) l Strong 
>               ; t2 <- urPDeriv (ur2, r2) l Strong
>               ; return $ [ ((ur' ++ ur2 ++ [(i, Choice dontcare ps)]) , (Pair (i:is) r1' r2), renv) |  (ur', r1', renv) <- t1 ] ++ t2
>               } 
>                 | otherwise   -> do 
>               { let ur2 =  ur `limit` fv r2 
>               ; t1 <-  urPDeriv (ur `limit` (fv r1), r1) l Strong 
>               ; return [ ((ur' ++ ur2 ++ [(i, Choice dontcare ps)]) , (Pair (i:is) r1' r2), renv) |  (ur', r1', renv) <- t1] 
>               }
>           }
>     ; Nothing | posEmpty r1 -> do 
>           { let ur2 =  ur `limit` fv r2 
>           ; t1 <- urPDeriv (ur `limit` (fv r1), r1) l rlvl
>           ; t2 <- urPDeriv (ur2, r2) l rlvl 
>           ; return $ [ ((ur' ++ ur2) , (Pair (i:is) r1' r2), renv) |  (ur', r1', renv) <-  t1 ] ++ t2
>           }
>               | otherwise   -> do 
>           { t1 <- urPDeriv (ur `limit` (fv r1), r1) l rlvl
>           ; return [ ((ur' ++ ur `limit` (fv r2)) , (Pair (i:is) r1' r2), renv) |  (ur', r1', renv) <- t1 ]
>           }
>     }
> urPDeriv (ur, Choice (i:is) rs) l rlvl = 
>    case lookup i ur of
>      { Just p ->  
>          case pderiv p l of
>          { [] -> return []
>          ; ps -> do 
>             { let ur' = updateUR i (Choice dontcare ps) ur
>             ; ts <- mapM (\ r -> urPDeriv (ur', r) l Strong) rs
>             ; return $ concat ts 
>             -- todo:move i:is to each r
>             }
>          }
>      ; Nothing -> do 
>          { ts <- mapM (\ r -> urPDeriv (ur, r) l rlvl) rs
>          ; return $ concat ts
>          }
>      }
> urPDeriv (ur, Star (i:is) r) l rlvl  = 
>     case lookup i ur of 
>       { Just p -> 
>          case pderiv p l of
>          { [] -> return []
>          ; ps -> do 
>             { let ur' = updateUR i (Choice dontcare ps) ur
>             ; t <- urPDeriv (ur',r) l Strong
>             ; return [ (ur'', Pair (i:is) r' (Star (i:is) r), renv)  
>                        | (ur'', r', renv) <- t ]
>             }
>          }
>       ; Nothing -> do 
>            { t <- urPDeriv (ur,r) l rlvl
>            ; return [ (ur', Pair (i:is) r' (Star (i:is) r), renv)  
>                        | (ur', r', renv) <- t ]
>            }
>       }
> urPDeriv ur c rlvl  = error $ "unhandled input: " ++ (show ur) ++ "/" ++ (show c)




> {- replaced by the above forumation, combining urPDeriv and urPDerivS by parameterizing S
> urPDeriv :: (UReq, Re) -> Char -> Int -> [(UReq, Re, REnv)]
> urPDeriv (ur, Eps (i:is)) l next_i
>   | i `inUR` ur = [ ((updateUR i r' ur), Eps [next_i], IM.singleton i [RASt (Ch [next_i] l) Strong]) 
>                      | let r = fromJust (lookupUR i ur), r' <- pderiv r l ]
>   | otherwise   = [ (ur, Eps [next_i], IM.singleton i [RASt (Ch [next_i] l) Weak]) ]
> urPDeriv (ur, (Ch (i:is) l)) l' next_i = 
>   case lookup i ur of 
>     { Just r | l == l' -> [ ((updateUR i r' ur), (Eps (i:is)), IM.empty )
>                            | r' <- pderiv r l ]
>              | l /= l' -> [ ((updateUR i r' ur), (Eps (i:is)), IM.singleton i [RATr (Ch [next_i] l') Strong]) | r' <- pderiv r l]
>     ; Nothing | l == l' -> [ (ur, Eps (i:is), IM.empty ) ]
>               | l /= l' -> [ (ur, Eps (i:is), IM.singleton i [RATr (Ch [next_i] l') Weak] ) ] 
>     }
> urPDeriv (ur, Pair (i:is) r1 r2) l next_i =
>    case lookup i ur of 
>     { Just p -> 
>         case pderiv p l of
>           { [] -> [] 
>           ; ps  | posEmpty r1 -> [ ((ur' ++ ur `limit` (fv r2) ++ [(i, Choice dontcare ps)]) , (Pair (i:is) r1' r2), renv) |  (ur', r1', renv) <- urPDerivS (ur `limit` (fv r1), r1) l next_i ] ++ (urPDerivS (ur `limit` (fv r2), r2) l next_i)
>                 | otherwise   -> [ ((ur' ++ ur `limit` (fv r2) ++ [(i, Choice dontcare ps)]) , (Pair (i:is) r1' r2), renv) |  (ur', r1', renv) <- urPDerivS (ur `limit` (fv r1), r1) l next_i] 
>           }
>     ; Nothing | posEmpty r1 -> [ ((ur' ++ ur `limit` (fv r2)) , (Pair (i:is) r1' r2), renv) |  (ur', r1', renv) <- urPDeriv (ur `limit` (fv r1), r1) l next_i ] ++ (urPDeriv (ur `limit` (fv r2), r2) l next_i)
>               | otherwise   -> [ ((ur' ++ ur `limit` (fv r2)) , (Pair (i:is) r1' r2), renv) |  (ur', r1', renv) <- urPDeriv (ur `limit` (fv r1), r1) l next_i ]
>     }
> urPDeriv (ur, Choice (i:is) rs) l next_i = 
>    case lookup i ur of
>      { Just p ->  
>          case pderiv p l of
>          { [] -> []
>          ; ps -> let ur' = updateUR i (Choice dontcare ps) ur
>                  in concatMap (\ r -> urPDerivS (ur', r) l next_i) rs -- todo:move i:is to each r
>          }
>      ; Nothing -> concatMap (\ r -> urPDeriv (ur, r) l next_i) rs 
>      }
> urPDeriv (ur, Star (i:is) r) l next_i = 
>     case lookup i ur of 
>       { Just p -> 
>          case pderiv p l of
>          { [] -> []
>          ; ps -> let ur' = updateUR i (Choice dontcare ps) ur
>                  in [ (ur'', Pair (i:is) r' (Star (i:is) r), renv)  
>                        | (ur'', r', renv) <- urPDerivS (ur',r) l next_i ]
>          }
>       ; Nothing -> [ (ur', Pair (i:is) r' (Star (i:is) r), renv)  
>                        | (ur', r', renv) <- urPDeriv (ur,r) l next_i ]
>       }
> urPDeriv ur c next_i = error $ "unhandled input: " ++ (show ur) ++ "/" ++ (show c)


urPDeriv with Strong recommendation

> urPDerivS :: (UReq, Re) -> Char -> Int -> [(UReq, Re, REnv)]
> urPDerivS (ur, Eps (i:is)) l next_i
>   | i `inUR` ur = [ ((updateUR i r' ur), Eps [next_i], IM.singleton i [RASt (Ch [ next_i] l) Strong]) 
>                      | let r = fromJust (lookupUR i ur), r' <- pderiv r l ]
>   | otherwise   = [ (ur, (Eps [next_i]), IM.singleton i [RASt (Ch [ next_i] l) Strong]) ]
> urPDerivS (ur, (Ch (i:is) l)) l'  next_i = 
>   case lookup i ur of 
>     { Just r | l == l' -> [ ((updateUR i r' ur), (Eps (i:is)), IM.empty )
>                            | r' <- pderiv r l ]
>              | l /= l' -> [ ((updateUR i r' ur), (Eps (i:is)), IM.singleton i [RATr (Ch [ next_i] l') Strong]) | r' <- pderiv r l]
>     ; Nothing | l == l' -> [ (ur, Eps (i:is), IM.empty ) ]
>               | l /= l' -> [ (ur, Eps (i:is), IM.singleton i [RATr (Ch [ next_i] l') Strong] ) ] 
>     }
> urPDerivS (ur, Pair (i:is) r1 r2) l  next_i =
>    case lookup i ur of 
>     { Just p -> 
>         case pderiv p l of
>           { [] -> [] 
>           ; ps  | posEmpty r1 -> [ ((ur' ++ ur `limit` (fv r2) ++ [(i, Choice dontcare ps)]) , (Pair (i:is) r1' r2), renv) |  (ur', r1', renv) <- urPDerivS (ur `limit` (fv r1), r1) l next_i ] ++ (urPDerivS (ur `limit` (fv r2), r2) l next_i)
>                 | otherwise   -> [ ((ur' ++ ur `limit` (fv r2) ++ [(i, Choice dontcare ps)]) , (Pair (i:is) r1' r2), renv) |  (ur', r1', renv) <- urPDerivS (ur `limit` (fv r1), r1) l next_i ] 
>           }
>     ; Nothing | posEmpty r1 -> [ ((ur' ++ ur `limit` (fv r2)) , (Pair (i:is) r1' r2), renv) |  (ur', r1', renv) <- urPDerivS (ur `limit` (fv r1), r1) l next_i] ++ (urPDerivS (ur `limit` (fv r2), r2) l next_i)
>               | otherwise   -> [ ((ur' ++ ur `limit` (fv r2)) , (Pair (i:is) r1' r2), renv) |  (ur', r1', renv) <- urPDerivS (ur `limit` (fv r1), r1) l next_i]
>     }
> urPDerivS (ur, Choice (i:is) rs) l next_i = 
>    case lookup i ur of
>      { Just p ->  
>          case pderiv p l of
>          { [] -> []
>          ; ps -> let ur' = updateUR i (Choice dontcare ps) ur
>                  in concatMap (\ r -> urPDerivS (ur', r) l next_i) rs -- todo:move i:is to each r
>          }
>      ; Nothing -> concatMap (\ r -> urPDerivS (ur, r) l next_i) rs 
>      }
> urPDerivS (ur, Star (i:is) r) l next_i = 
>     case lookup i ur of 
>       { Just p -> 
>          case pderiv p l of
>          { [] -> []
>          ; ps -> let ur' = updateUR i (Choice dontcare ps) ur
>                  in [ (ur'', Pair (i:is) r' (Star (i:is) r), renv)  
>                        | (ur'', r', renv) <- urPDerivS (ur',r) l next_i]
>          }
>       ; Nothing -> [ (ur', Pair (i:is) r' (Star (i:is) r), renv)  
>                        | (ur', r', renv) <- urPDerivS (ur,r) l next_i]
>       }
> urPDerivS ur c next_i = error $ "unhandled input: " ++ (show ur)  ++ "/" ++ (show c)
> -}


return all labels annotation of a re

> fv :: Re -> [Int]
> fv (Eps is) = is
> fv (Ch is _) = is
> fv (Pair is r1 r2) = is ++ fv r1 ++ fv r2
> fv (Choice is rs)  = is ++ concatMap fv rs
> fv (Star is r) = is ++ fv r
> fv _ = []


retrict the user req based on a set of labels

> limit :: UReq -> [Int] -> UReq
> limit ur is = filter (\(i,_) -> i `elem` is) ur


``` 


```

applying REnv to a Re


> apply_ :: REnv -> Re -> Re 
> apply_ renv r = let is = concatMap getLabels $ resInROps (concatMap snd (IM.toList renv)) -- fixme fromJust
>                     max_i = maximum $ (getLabels r) ++ is
>                 in run_ (Env max_i) (apply renv r)

> apply :: REnv -> Re -> State Env Re 
> apply renv s = 
>   let r = simp  s
>   in case getLabel r of 
>                {  (i:is) -> -- The first one is always the orginal label annotated to the regexp. The tail could contain those being collapsed because of pderiv op
>                  case IM.lookup i renv of 
>                    { Just rs -> do 
>                          { r' <- apply' renv r
>                          ; let adds = map (\ (RATr t _ ) -> t) $ filter isRATr rs
>                                rs'  = filter isRASt rs
>                          ; apps <- mapM (\ (RASt t _ ) -> apply renv t) rs'
>                          ; let r''  = app r' apps 
>                          ; case adds of 
>                             { (_:_) -> do 
>                               { next_i <- incMaxId 
>                               ; return $ Choice (i:is) ((annotate [next_i] r''):adds)
>                               }
>                             ; [] -> return r'' }
>                          }
>                    ; Nothing -> apply' renv r
>                    }
>                ; [] -> error ("apply: getLabel is applied to a regular ex which has no label. " ++ (show r))
>                }

> apply' :: REnv -> Re -> State Env Re
> apply' renv (Pair is r1 r2) = do { r1' <- apply renv r1 
>                                  ; r2' <- apply renv r2 
>                                  ; return $ Pair is r1' r2' }
> apply' renv (Choice is rs) = do { rs' <- mapM (apply renv) rs
>                                 ; return $ Choice is rs' 
>                                 }
> apply' renv (Star is r) = do { r' <- apply renv r
>                              ; return $ Star is r' }
> apply' _ r = return r

> app :: Re -> [Re] -> Re
> app r [] = r
> app r (t:ts) = let is = getLabel r 
>                in app (Pair is r (annotate is t)) ts


> combineEnv :: REnv -> REnv -> REnv 
> combineEnv renv1 renv2 = IM.unionWith (\x y -> (x ++ y)) renv1 renv2 -- don't nub here.

> extend :: REnv -> [Int] -> ROp -> REnv
> extend renv [] _ = renv
> extend renv (i:_) e@(RATr r lvl) = -- we only care about the original label
>      case IM.lookup i renv of 
>       { Just rs | not (e `elem` rs) ->  IM.adjust (\_ -> rs++[RATr r lvl]) i renv 
>                 | otherwise -> renv
>       ; Nothing -> IM.insert i [RATr r lvl] renv
>       }



> showL :: Show a => [a] -> IO ()
> showL xs = do 
>   { mapM_ (\x -> print x >> putStrLn "" ) xs }  




OLD STUFF: the norm and denorm are hard to explain


> {-

> refine :: [URPair] -> Doc -> [Re] 


```
 -------------------------------------------------------------------------------------------------- (Eps)
  { (\gamma_1, r_1), ..., (\gamma_n, r_n) } \models \epsilon : 
         { (\gamma_i, r_i) | (\gamma_i,r_i) \in { (\gamma_1, r_1), ..., (\gamma_n, r_n) } \wedge   
                              \epsilon \in \gamma_i (x) \forall x in \gamma_i \wedge 
                              \epsilon \in r_i }  ++ 
                              (\gamma_i,r_i?) \in { (\gamma_1, r_1), ..., (\gamma_n, r_n) } \wedge   
                              \epsilon \in \gamma_i (x) \forall x in \gamma_i \wedge 
                              \epsilon \not \in r_i }  

```

> refine urs [] = 
>   let urs' = filter (\ (URPair u r rec) -> allAccEps u ) urs 
>       (urs_rAccEps, urs_rNAccEps) = partition (\ (URPair u r rec) -> posEmpty r) urs'
>       rNAccEpsEps = map (\(URPair u r rec) -> let x = topLabel r in (Choice x [r, Eps x])) urs_rNAccEps
>       rAccEps = map (\ (URPair _ r _) -> r) urs_rAccEps
>   in rAccEps ++ rNAccEpsEps

```
   { (\gamma_1, r_1), ..., (\gamma_n, r_n) } / l =     { (\gamma_1', r_1'), ..., (\gamma_m', r_m') }
   
    { (\gamma_1', r_1'), ..., (\gamma_m', r_m') } \models v : { q_1', ... q_k' }
   
   { r_1, ..., r_n } ~>_norm  { (l_1, \bar{r}_1), ... (l,  \bar{r} ), ...,  (l_j, \bar{r}_j) } -- TODO: check why no need to takes in the user req? ANS: yes. no need, other monomials is not activated by the input lv.
  
    { (l_1, \bar{r}_1), ... (l,  \bar{q'} ), ...,  (l_j, \bar{r}_j) } ~>_denorm {q_1, ..., q_h }
 -------------------------------------------------------------------------------------------------- (Norm)
  { (\gamma_1, r_1), ..., (\gamma_n, r_n) } \models (lv) : {q_1, ..., q_h }
```

> refine urs (l:w) = 
>   let urs' = urPDeriv urs l 
>       qs'  = refine urs' w        
>       ms   = foldl (\m1 m2 -> m1 `unionLNF` m2) emptyLNF (map (\ (URPair _ r _) -> norm r) urs)  -- all the nfa states should be grouped into the same normal form, e.g. [ a, (a|b) ] ~> [a, b]
>       ms'  = combine ms l qs'
>       qs   = denorm ms'
>   in qs
>   where combine :: LNF -> Char -> [Re] -> LNF
>         combine = undefined

extracts the topmost level label

> -}

> {-

> topLabel :: Re -> [Int]
> topLabel (Eps x) = x
> topLabel (Ch x _) = x
> topLabel (Choice x _) = x
> topLabel (Pair x _ _) = x
> topLabel (Star x _) = x
> topLabel Phi = dontcare


normalization
  $p \norm m1 | ... | mn$  
                 
     where m_i denotes the monomial of shape (l_i, [r1,...,rn])

de-normalization
  $ m1 | ... | mn \denorm p$ 


1) l, \epsilon_i r -> li r
2) { r1 r, r2 r } => (r1|r2) r
3)  r_i (r'_i)*_j and r_i \subseteq r_i' ->    r_i*_j    () \in lnf 
                       ^^^^^^^^^^^^^^^^^^      r_i+_j    otherwise    -- this or directly update the l_i to (l|l')_i? for all location of i in r?
4) (r*|\epsilon) r' -> r* r'                 
    

The linear normal form


lnf ::= { (l1,\bar{r1}), ... , (ln, \bar{rn}) } U {\eps}  ||
        { (l1,\bar{r1}), ... , (ln, \bar{rn}) } 

> data LNF = WithEps [Int] ( M.Map Char [Re] -- Maping l -> [r]
>                          , M.Map Re [Re] ) -- Mapping r* -> prefix 
>          | WithoutEps [Int] ( M.Map Char [Re] -- Mapping l -> [r]
>                             , M.Map Re [Re] ) -- Mapping r* -> prefix
>           deriving Show

what is in addition is the dictionary that maps the trailing r* back to the prefix for all the monomials. It will be used to 
denormalization


> emptyLNF = WithoutEps [] (M.empty, M.empty)

> unionLNF :: LNF -> LNF -> LNF 
> unionLNF = undefined



norm r = if () \in r then (norm' r) ++ { () }  else (norm' r)

> norm :: Re -> LNF                            
> norm Phi = error "applying norm to Phi"
> norm r | posEmpty r = WithEps x (norm' x r)
>        | otherwise  = WithoutEps x (norm' x r)
>   where x = getLabel r
              

norm' r = groupBy (eq . last) [(l, r') | l \in \sigma(r), r' \in pderiv r l]

> norm' :: [Int] -> Re -> (M.Map Char [Re], M.Map Re [Re])
> norm' x r = let ms = [ (l, r') | l <- sigma r, r' <- pderiv r l ]
>             in (foldl (\m (l,r) -> upsert l [r] (++) m) M.empty ms, foldl (\m (r,l) -> upsert r [l] (++) m) M.empty (map (\(l,r) -> (last_ r, Pair x (Ch x l) (init_ r))) ms))

last_ returns the right most re in a sequence of Re

> last_ :: Re -> Re 
> last_ (Pair x r1 r2) = last_ r2
> last_ r = r

> init_ :: Re -> Re
> init_ (Pair x r1 r2) = let r2' = (init_ r2)
>                        in case r2' of { Eps _ -> r1; _ -> Pair x r1 r2' }
> init_ r = Eps dontcare

append_ appends two Re(s) by sequence

> append_ :: [Int] -> Re -> Re -> Re
> append_ _ (Pair y r1 r2) r3 = Pair y r1 (append_ y r2 r3)
> append_ x r1 r2 = Pair x r1 r2

> upsert :: Ord k => k -> v -> (v -> v -> v) -> M.Map k v -> M.Map k v
> upsert k v f m = case M.lookup k m of 
>                  { Just v' -> M.adjust (\_ -> f v' v) k m 
>                  ; Nothing -> M.insert k v m }

> lookupMN :: Char -> LNF -> Maybe [Re]

> lookupMN c (WithEps x (m1,m2)) = M.lookup c m1
> lookupMN c (WithoutEps x (m1,m2)) = M.lookup c m1

> updateMN :: Char -> [Re] -> LNF -> LNF
> updateMN c rs (WithEps x (m1,m2)) = 
>    let ps = map (\r -> (last_ r, Pair x (Ch x c) (init_ r))) rs   -- the tails and the head (prefix + label)
>    in WithEps x (M.adjust (\_ -> rs) c m1, foldl (\m (t,h) -> upsert t [h] (++) m) m2 ps)  -- the subfix r' might not be in m2
> updateMN c rs (WithoutEps x (m1,m2)) = 
>    let  ps = map (\r -> (last_ r, Pair x (Ch x c) (init_ r))) rs   -- the tails and the head (prefix + label)
>    in WithoutEps x (M.adjust (\_ -> rs) c m1, foldl (\m (t,h) -> upsert t [h] (++) m) m2 ps)  -- the subfix r' might not be in m2

> insertMN :: Char -> [Re] -> LNF -> LNF
> insertMN c rs (WithEps x (m1,m2)) = 
>    let ps = map (\r -> (last_ r, Pair x (Ch x c) (init_ r))) rs   -- the tails and the head (prefix + label)  
>    in WithEps x (M.insert c rs m1, foldl (\m (t,h) -> upsert t [h] (++) m) m2 ps) 
> insertMN c rs (WithoutEps x (m1,m2)) = 
>    let ps = map (\r -> (last_ r, Pair x (Ch x c) (init_ r))) rs   -- the tails and the head (prefix + label)  
>    in WithoutEps x (M.insert c rs m1, foldl (\m (t,h) -> upsert t [h] (++) m) m2 ps)

> singleton :: [Int] -> Doc -> Re 
> singleton x cs = foldr (\l r -> Pair x (Ch x l) r) (Eps x) cs


return a choice if the list is non-singleton

> mkChoice :: [Int] -> [Re] -> Re 
> mkChoice x [r] = r
> mkChoice x rs = Choice x rs

denorm (\bar{m}|()) = let (pluses, nonpluses) = splitBy isPlusMonomial $ denorm' \bar{m}                           
                      in [ (mkStar plus) | plus <- pluses ] ++ nonpluses
                          
denorm \bar{m} = let (pluses, nonpluses) = splitBy isPlusMonomial $ denorm' \bar{m}
                 in [ (mkPlus plus) | plus <- pluses ]  ++ nonpluses


> denorm :: LNF -> [Re]
> denorm (WithEps x (m1,m2)) = 
>    let (plusMonoGrp, nonPlusMonoGrp) = part m2 
>        ps = map mkStar (M.toList plusMonoGrp)         
>        nps = map (\(tl, its) -> append_ x (mkChoice x its) tl) (M.toList nonPlusMonoGrp)
>    in (ps ++ nps)
> denorm (WithoutEps x (m1,m2)) = 
>    let (plusMonoGrp, nonPlusMonoGrp) = part m2 
>        ps = map mkPlus (M.toList plusMonoGrp)         
>        nps = map (\(tl, its) -> append_ x (mkChoice x its) tl) (M.toList nonPlusMonoGrp)
>    in (ps ++ nps)


> mkStar :: (Re, [Re]) -> Re
> mkStar = fst

> mkPlus :: (Re, [Re]) -> Re
> mkPlus (Star x r,its) = Pair x r (Star x r)


partition map by plus monomial and non plus monomial

> part :: M.Map Re [Re] -> (M.Map Re [Re] , M.Map Re [Re])
> part m = M.partitionWithKey (\ r rs -> isPlusMN rs r ) m


a monomial is a plus mono iff m = (p1|...|pn, r*) and (p1|...|pn) \equiv r and r 

isPlus (p1|...|pn) r* = (p1|...|pn) <= r and r <= (p1|...|pn)

> isPlusMN :: [Re] -> Re -> Bool
> isPlusMN ps (Star x r) = ((Choice dontcare ps) `subsumedBy` r) && (r `subsumedBy` (Choice dontcare ps))
> isPlusMN ps _ = False

the containment check

> subsumedBy :: Re -> Re -> Bool
> subsumedBy r1 r2 = subsumedBy' M.empty r1 r2

> data Leq = Leq Re Re deriving (Eq, Ord, Show)

> subsumedBy' :: M.Map Leq () -> Re -> Re -> Bool
> subsumedBy' env Phi _ = True
> subsumedBy' env r1 r2 = 
>   case M.lookup (Leq r1 r2) env of   
>    { Just _  -> True  
>    ; Nothing | posEmpty r1 && not (posEmpty r2) -> False
>              | otherwise -> let env' = M.insert (Leq r1 r2)  () env
>                             in  all (\l -> subsumedBy' env' (deriv r1 l) (deriv r2 l)) (sigma (Choice dontcare [r1,r2]))
>    }

                          
                          
denorm' \bar{m} = groupBy (eq . snd) [(l, r/l) | l \in \sigma(r)]

isPlusMonomial (l,p) = l \in (choiceToList p)

mkStar ms = let fs = map fst ms  
                (Star r) = snd (head ms)
            in if (sort fs) == (sort (choiceToList r)) then (Star r) else ms

mkPlus ms = let fs = map fst ms  
                (Star r) = snd (head ms)
            in if (sort fs) == (sort (choiceToList r)) then (r, (Star r)) else ms


> -}
