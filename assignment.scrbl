#lang scribble/manual
@require[scribble-math]
@require[scribble-math/dollar]
@require[racket/runtime-path]

@require["../../lib.rkt"]
@define-runtime-path[hw-file "hw10.lean"]


@title[#:tag "hw10" #:style (with-html5 manual-doc-style)]{Homework 10}

@bold{Released:} @italic{Wednesday, March 22, 2023 at 6:00pm}

@bold{Due:} @italic{Wednesday, March 29, 2023 at 6:00pm}

@nested[#:style "boxed"]{
What to Download:

@url{https://github.com/logiccomp/s23-hw10/raw/main/hw10.lean}
}

Please start with this file, filling in where appropriate, and submit your homework to the @tt{hw10} assignment on Gradescope. This page has additional information, and allows us to format things nicely.

@bold{To do this assignment in the browser: @link["https://github.com/codespaces/new?machine=basicLinux32gb&repo=578247840&location=EastUs&ref=main&devcontainer_path=.devcontainer%2Fdevcontainer.json"]{Create a Codespace}.}



@section{Verifying Compilers with Simulations}

Earlier, we've seen simpler compiler correctness proofs of languages that were just arithmetic, or perhaps, arithmetic with variables. In this assignment, we'll introduce slightly more interesting languages, in order to demonstrate the main technique used in proving compilers correct: simulation relations. 

Compiler correctness, at its essence, amounts to the following theorem:

Given a source program @${E_s}, if it is compiled to a target program @${E_t}, then runinng @${E_s \overset{*}{\rightarrow} v_s} (to a source value @${v_s}) and running the target program @${E_t \overset{*}{\rightarrow} v_t} (to a target value @${v_t}) should result in related (or equivalent) target values. In languages with side effects (printing, network, etc), they should also produce the same effects. 

The most common way of proving this is with a so-called "simulation" relation, which describes a relationship between source a target programs that should hold @italic{as the programs evaluate}. So rather than trying to prove, all at once, that @${v_s} is equivalent to @${v_t} (the final values after runinng the source and target program), we instead just show that after each step, the simulation relation still holds. Technically, what it will say is that if the source term takes a step, then after zero or more steps the target will reach a term that is in the simulation relation with the new source term. This allows the target to take more (or fewer) steps than the source. Provided this relation holds as we go, and the relation relates equal values to values, once the programs terminate, the relation will give us what we need, that @${v_s} is equivalent to @${v_t}.

In this assignment, you will prove a simulation proof for a compiler that compiles booleans to numbers, in a small functional language that has functions, variables, function application, and either booleans (and `and`) or numbers (and `plus` and `minus`). By including functions (which are untyped), we end up including a lot of the complexity of more interesting languages (e.g., recursion, etc), but without adding lots of cases to our syntax (which would translate to more cases of the proof).

We first give you a background definitions, which we talked about in class (in @[seclink "l27" "L27, 3/22"]).

@minted-file-part["lean" "1" hw-file]

And definitions for the source & target language, which includes substitution functions to handle function application:

@minted-file-part["lean" "2" hw-file]

We also give you the compiler:

@minted-file-part["lean" "3" hw-file]

And the simulation relation:

@minted-file-part["lean" "4" hw-file]

@section{Problem 1: Helper theorems relating Rstar to TStep}

In this first problem, you'll prove various helper theorems relating to the evaluation of the target (number containing) language. 

@minted-file-part["lean" "5" hw-file]

@section{Problem 2: Substitution commutes with compile.}

  In this problem, you will prove that substituting and then 
  compiling is the same as compiling and then substituting. 
  This will be a necessary result in the `beta` case of `sim_step`.

  Think about whether the expression being substituted, or the 
  expression substituted into (e or body) make more sense to do
  induction on. Also: in the cases where variable comparison is 
  used (var & lam), remember L23 (3/13).

@minted-file-part["lean" "6" hw-file]

@section{Problem 3: Show that the simulation respects compiler.}

  In some relations, this is involved: in ours, this should be 
  trivial! But it is a necessary step, as logically, it is how we
  start our argument: first, we show that the source & target term are
  in the relation. Then we should that at each step, they remain; 
  finally, we should that when they terminate, they terminate at related
  values.

@minted-file-part["lean" "7" hw-file]

@section{Problem 4: Simulation is preserved over reduction}

  This is the heart of the proof. It says that for a single
  step of the source, after any number of steps of the target,
  there is some target term that is related again. i.e., we can 
  always get back to a pair of related terms. We will use this 
  iteratively in the next proof. 

  Be sure to use the theorems you did in Problem 1 & Problem 2, 
  and as a hint: you will want to do induction on the SSTep relation.

  @minted-file-part["lean" "8" hw-file]

  @section{Problem 5: Simulation is preserved over multiple steps}


  This problem shows that if we take many steps at the source, 
  the result from the previous theorem still holds. It is 
  much easier, since we can appeal to the single step result
  (where most of the work is done). 

  @minted-file-part["lean" "9" hw-file]

  @section{Problem 6: Prove the compiler is correct}

  @minted-file-part["lean" "10" hw-file]