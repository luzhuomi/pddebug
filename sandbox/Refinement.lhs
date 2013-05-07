

The regular expression refinement algorithm

Inspired by the type checking system and type inference algorithm found in programming language research communities. \cite{TODO}

= Type checking and Type inference algorithm =

== Type checking judgement ==
$\gamma \vdash e : t$ 
Given the type environemnt $\gamma$, the program expression e and the type $t$, the above is deducable if $e$ has type $t$ under the type environment $\gamma$

Note that the type checking is a relation, where $\gamma$, $e$ and $t$ are the inputs.

== Type inference judgement == 

$\gamma \models e : t$

Given the type environment \gamma and the program expression e the algorithm reconstructs the type t.

Note that the type inference is considered an function, where \gamma and e are the inputs.

=== Type inference correctness === 

$\gamma \models e : t$ 
implies 
$\gamma \vdash e : t$ 




= Regular expression debugging and reconstruction =

== The connection == 

Pointed out the XDuce work, we consider the correspondence between the program expression $e$ and the document $d$,
the type $t$ and the regular expression $r$.

 * The word problem  $d \in r$ corresponds to the type checking problem.

== The difference == 

 * The matching problem 

 $$ d \in r \Longrightarrow \Delta $$ 

where r is annotated with label at each AST level. $\Delta$ maps labels to sub-matches.


== The mechanism == 

We use derivative (or partial derivative) operations to implement the word problem and the sub matching problem. See our recent papers (PPDP 12 )


== The debugging algorithm == 

Refer to the PDDebug.lhs

== The Refinement checking judgement == 

> module Main where

=== The problem === 

Let  $\gamma$ denote the user specification, $d$ denote the input document , $r$ the pattern and  $r'$ the refined pattern, 
we use the judgement 
$$\gamma, r \vdash d : r'$$ 
to denote that under the user spec $\gamma$ , $r'$ is a replacement of $r$ that accepts $d$.

 * The user requirement 

\gamma ::= { (i, r) , ... , }
i ::= 1,2,3,...

> newtype Req i = Req [(i, RE)]

> lookupReq :: Eq i => i -> Req i -> Maybe RE
> lookupReq i (Req env) = lookup i env

 * The Regular expression 
             
r ::= ()^i || (r|r)^i || (rr)^i || (r*)^i || l^i || \phi^i 
                          
                          

=== The Replacement Relation ===
We use the following judgement to denote the replacement relation
$$ \gamma, r \turns d : t $$ 
where $\gamma$ is the user requirement, $r$ is the existing regular expression, $d$ is the input document and $t$ is the replacement regular expression.
It reads, under user requirement $\gamma$, $r$ can be replaced by $t$ which accepts $d$. 

There are two properties follows 

 1. $d\in r \Longrightarrow \Delta$ implies $ \Delta \vdash \gamma$ and $r \subseq t$.
 2. $d \not \in r$ implies $r \gamma\over\approximate t$  and $d \in t \Longrightarrow \Delta$ and $\Delta \vdash \gamma$.

The first property ensures that the replacement is subsuming the orginal regex $r$ if $d$ is already in $r$ and the matching result is conforming to the user requirement.
The second property ensures that if $d$ is not in $r$, the replacement shall have the same requirement-shape as the orginal one and conform to the user requirement. 

   d \in r
-------------------------
\emptyset, r \vdash d : r

   d \not \in r   d \in r'
-------------------------
\emptyset, r \vdash d : r'


----------------------------------------------
 {(i,t)} U \gamma, r^i \vdash 