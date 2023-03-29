/- ----------------------
   BACKGROUND DEFINITIONS
   ----------------------
-/

-- part 1
inductive Rstar {T : Type} (P : T -> T -> Prop) : T -> T -> Prop :=
| refl : forall a, Rstar P a a
| step : forall a b c, P a b -> Rstar P b c -> Rstar P a c

theorem RTrans {T : Type} {P : T -> T -> Prop} {a b c : T} : 
        Rstar P a b -> Rstar P b c -> Rstar P a c :=
  by intros H1
     revert c
     induction H1 <;> intros c H2 <;> simp <;> try assumption
     constructor
     assumption
     rename_i H
     apply H
     assumption

-- part 1
/- ------------------------
   SOURCE, TARGET, COMPILER
   ------------------------
-/
-- part 2

inductive Source :=
| b : Bool -> Source
| and : Source -> Source -> Source
| var : String -> Source
| lam : String -> Source -> Source
| app : Source -> Source -> Source

def Source.sub (e : Source) (x : String) (body : Source) :=
  match body with
  | b _ => body
  | and t1 t2 => and (e.sub x t1) (e.sub x t2)
  | var x' => if x == x' then e else body
  | app t1 t2 => app (e.sub x t1) (e.sub x t2)
  | lam x' body' => if x == x' then body
                    else lam x' (e.sub x body')

inductive SStep : Source -> Source -> Prop :=
| app : forall e e' a, SStep e e' ->
                  SStep (Source.app e a) (Source.app e' a)
| beta : forall x1 body e,
    SStep (Source.app (Source.lam x1 body) e)
        (e.sub x1 body)
| and1 : forall e1 e1' e2, SStep e1 e1' ->
                        SStep (Source.and e1 e2) (Source.and e1' e2)
| and2 : forall b e2 e2', SStep e2 e2' ->
                      SStep (Source.and (Source.b b) e2) (Source.and (Source.b b) e2')
| and : forall b1 b2, SStep (Source.and (Source.b b1) (Source.b b2))
                        (Source.b (b1 && b2))

inductive Target :=
| n : Nat -> Target
| plus : Target -> Target -> Target
| minus : Target -> Target -> Target
| var : String -> Target
| lam : String -> Target -> Target
| app : Target -> Target -> Target

def Target.sub (e : Target) (x : String) (body : Target) :=
  match body with
  | n _ => body
  | plus t1 t2 => plus (e.sub x t1) (e.sub x t2)
  | minus t1 t2 => minus (e.sub x t1) (e.sub x t2)
  | var x' => if x == x' then e else body
  | app t1 t2 => app (e.sub x t1) (e.sub x t2)
  | lam x' body' => if x == x' then body
                      else lam x' (e.sub x body')

inductive TStep : Target -> Target -> Prop :=
| app : forall e e' a, TStep e e' ->
                  TStep (Target.app e a) (Target.app e' a)
| beta : forall x1 body e,
    TStep (Target.app (Target.lam x1 body) e)
          (e.sub x1 body)
| plus1 : forall e1 e1' e2, TStep e1 e1' ->
                        TStep (Target.plus e1 e2) (Target.plus e1' e2)
| plus2 : forall e1 e2 e2', TStep e2 e2' ->
                        TStep (Target.plus e1 e2) (Target.plus e1 e2')
| plus : forall n1 n2, TStep (Target.plus (Target.n n1) (Target.n n2))
                        (Target.n (n1 + n2))
| minus1 : forall e1 e1' e2, TStep e1 e1' ->
                      TStep (Target.minus e1 e2) (Target.minus e1' e2)
| minus2 : forall e1 e2 e2', TStep e2 e2' ->
                      TStep (Target.minus e1 e2) (Target.minus e1 e2')
| minus : forall n1 n2, TStep (Target.minus (Target.n n1) (Target.n n2))
                          (Target.n (n1 - n2))


-- part 2

-- part 3
def Source.compile : Source -> Target 
| b true    => Target.n 1
| b false   => Target.n 0
| and b1 b2 => Target.minus (Target.plus (compile b1) (compile b2)) (Target.n 1)
| var x     => Target.var x
| app t1 t2 => Target.app (compile t1) (compile t2)
| lam x bdy => Target.lam x (compile bdy)

-- part 3
/- -------------------
   SIMULATION RELATION
   -------------------
-/
-- part 4
inductive sim : Source -> Target -> Prop :=
| comp : forall e, sim e e.compile
-- part 4

/- PROBLEM 1: Lifting steps to RStar

  These theorems will be necessary when proving `sim_step`. They
  show how even though TStep is not defined in terms of Rstar, 
  you can nonetheless lift many steps (using Rstar) into subterms.

  Note that all of these proofs should be very similar! So while it
  looks like a lot, once you do _one_, the rest should be quite easy.
-/

-- part 5
-- 7 lines 
theorem app_star : forall e1 e1' e2, Rstar TStep e1 e1' -> 
                  Rstar TStep (Target.app e1 e2) (Target.app e1' e2) :=
 by intros e1 e1' e2 h 
    induction h
    case refl t => constructor
    case step a b c t _ h => constructor
                             case a => apply TStep.app
                                       assumption
                             case a => assumption          


-- 7 lines
theorem plus_star1 : forall e1 e1' e2, Rstar TStep e1 e1' -> 
                  Rstar TStep (Target.plus e1 e2) (Target.plus e1' e2) :=
 by intros e1 e1' e2 h
    induction h
    case refl t => constructor
    case step a b c t _ h => constructor
                             case a => apply TStep.plus1
                                       assumption
                             case a => assumption            

-- 7 lines
theorem plus_star2 : forall e1 e2 e2', Rstar TStep e2 e2' -> 
                  Rstar TStep (Target.plus e1 e2) (Target.plus e1 e2') :=
 by intros e1 e1' e2 h
    induction h
    case refl t => constructor
    case step a b c t _ h => constructor
                             case a => apply TStep.plus2 
                                       assumption
                             case a => assumption           


-- 7 lines
theorem minus_star1 : forall e1 e1' e2, Rstar TStep e1 e1' -> 
                  Rstar TStep (Target.minus e1 e2) (Target.minus e1' e2) :=
 by intros e1 e1' e2 h
    induction h
    case refl t => constructor
    case step a b c t _ h => constructor
                             case a => apply TStep.minus1 
                                       assumption
                             case a => assumption        

-- 7 lines
theorem minus_star2 : forall e1 e2 e2', Rstar TStep e2 e2' -> 
                  Rstar TStep (Target.minus e1 e2) (Target.minus e1 e2') :=
 by intros e1 e1' e2 h
    induction h
    case refl t => constructor
    case step a b c t _ h => constructor
                             case a => apply TStep.minus2 
                                       assumption
                             case a => assumption        

-- part 5

/- PROBLEM 2: Substitution commutes with compile.

  In this problem, you will prove that substituting and then 
  compiling is the same as compiling and then substituting. 
  This will be a necessary result in the `beta` case of `sim_step`.

  Think about whether the expression being substituted, or the 
  expression substituted into (e or body) make more sense to do
  induction on. Also: in the cases where variable comparison is 
  used (var & lam), remember L23 (3/13).
-/
-- part 6

-- 15 lines
theorem compile_sub : forall (e : Source) x (body : Source),
  (e.sub x body).compile = Target.sub e.compile x body.compile :=
 by intros e x b
    induction b 
    case b a => simp [Source.sub]
                cases a
                case false => constructor
                case true => constructor
    case and a m q p => simp [Source.sub]   
                        simp [Target.sub]
                        rw [<- q]
                        rw [<- p]
                        constructor
    case var a => simp only [Source.sub, Target.sub] 
                  generalize r : (x == a) = q        
                  cases q 
                  case false => simp only []
                                rw [ite_false] 
                                rw [ite_false]
                  case true => simp only []
                               rw [ite_true]
                               rw [ite_true]  
    case lam str s h => simp only [Source.sub, Target.sub]
                        generalize r : (x == str) = q
                        cases q 
                        case false => simp only []
                                      rw [ite_false]
                                      rw [ite_false]
                                      rw [<- h]
                                      constructor
                        case true => simp only []
                                     rw [ite_true]
                                     rw [ite_true]    
    case app a1 a2 h1 h2 => simp only [Source.sub]
                            simp [Target.sub]
                            rw [<- h1]
                            rw [<- h2]
                            constructor                     
                            
                            

                                          

                

-- part 6
/- PROBLEM 3: Show that the simulation respects compiler.

  In some relations, this is involved: in ours, this should be 
  trivial! But it is a necessary step, as logically, it is how we
  start our argument: first, we show that the source & target term are
  in the relation. Then we should that at each step, they remain; 
  finally, we should that when they terminate, they terminate at related
  values.
-/
-- part 7

-- 1 line
theorem compile_sim : forall t,
  sim t t.compile := 
 by apply sim.comp
    

-- part 7
/- PROBLEM 4: Simulation is preserved over reduction

  This is the heart of the proof. It says that for a single
  step of the source, after any number of steps of the target,
  there is some target term that is related again. i.e., we can 
  always get back to a pair of related terms. We will use this 
  iteratively in the next proof. 

  Be sure to use the theorems you did in Problem 1 & Problem 2, 
  and as a hint: you will want to do induction on the SSTep relation.
  exists (Source.compile (Source.app e' a))
                            constructor
                            case left => cases sim1
                                         case comp => simp [Source.compile]
                                                      apply app_star
                                                      sorry
                            case right => apply compile_sim   
-/
-- part 8

-- 67 lines
theorem sim_step : forall t1 t1',
  SStep t1 t1' ->
  forall t2,
  sim t1 t2 ->
  exists t2', Rstar TStep t2 t2' /\ sim t1' t2' := 
 by intros t1 t1' stept1
    induction stept1 <;> intros t2 sim1 
    case app e e' a _ h => cases sim1
                           case comp => cases (h _ (sim.comp e))
                                        case intro w H => cases H
                                                          case intro rs ss1 => exists (Source.compile (Source.app e' a))
                                                                               apply And.intro
                                                                               case left => simp [Source.compile]
                                                                                            apply app_star
                                                                                            cases ss1
                                                                                            assumption
                                                                               case right => apply compile_sim             
    case beta x s b => exists (Source.compile (Source.sub b x s))
                       cases sim1
                       case comp => apply And.intro
                                    case left => rw [compile_sub]
                                                 simp [Source.compile] 
                                                 apply Rstar.step
                                                 case a => apply TStep.beta
                                                 case a => apply Rstar.refl
                                    case right => apply compile_sim  
    case and1 e1 e1' e2 _ h => cases sim1
                               case comp => cases (h _ (sim.comp e1))
                                            case intro w H => cases H
                                                              case intro rs ss1 => exists (Source.compile ((Source.and e1' e2)))
                                                                                   apply And.intro
                                                                                   case left => simp [Source.compile]
                                                                                                apply minus_star1
                                                                                                case a => apply plus_star1
                                                                                                          cases ss1
                                                                                                          assumption
                                                                                   case right => apply compile_sim       
    case and2 e1 e1' e2 _ h => cases sim1
                               case comp => cases (h _ (sim.comp e1'))
                                            case intro w H => cases H
                                                              case intro rs ss1 => exists (Source.compile (Source.and (Source.b e1) e2))
                                                                                   apply And.intro
                                                                                   case left => simp [Source.compile]
                                                                                                apply minus_star1
                                                                                                apply plus_star2
                                                                                                cases ss1
                                                                                                assumption
                                                                                   case right => apply compile_sim       
    case and b1 b2 => cases sim1
                      case comp => exists (Source.compile (Source.b (b1 && b2))) 
                                   apply And.intro 
                                   case left => simp [Source.compile]
                                                cases b1
                                                cases b2
                                                case false.false => simp [Source.compile]
                                                                    apply Rstar.step
                                                                    case a => apply TStep.minus1
                                                                              apply TStep.plus
                                                                    case a => apply Rstar.step
                                                                              apply TStep.minus
                                                                              apply Rstar.refl                   
                                                case false.true => simp [Source.compile]
                                                                   apply Rstar.step
                                                                   case a => apply TStep.minus1
                                                                             apply TStep.plus 
                                                                   case a => apply Rstar.step
                                                                             apply TStep.minus
                                                                             apply Rstar.refl
                                                cases b2                                             
                                                case true.false => simp [Source.compile]
                                                                   apply Rstar.step
                                                                   case a => apply TStep.minus1
                                                                             apply TStep.plus 
                                                                   case a => apply Rstar.step
                                                                             apply TStep.minus
                                                                             apply Rstar.refl                   
                                                case true.true => simp [Source.compile]
                                                                  apply Rstar.step
                                                                  case a => apply TStep.minus1
                                                                            apply TStep.plus 
                                                                  case a => apply Rstar.step
                                                                            apply TStep.minus
                                                                            apply Rstar.refl                                 
                                   case right => apply compile_sim
                                                                                 
                                    
                                                
                                                  



                                                                  
                                                                               

                                                                               
                                              

                                                                  


-- part 8
/- PROBLEM 5: sim_step lifts to many steps.

  This problem shows that if we take many steps at the source, 
  the result from the previous theorem still holds. It is 
  much easier, since we can appeal to the single step result
  (where most of the work is done). 
-/
-- part 9

-- 15 lines
theorem step_sim_star : forall t1 t1',
  Rstar SStep t1 t1' ->
  forall t2,
  sim t1 t2 ->
  exists t2', Rstar TStep t2 t2' /\ sim t1' t2' := 
 by intros t1 t1' rst1
    induction rst1 <;> intros t2 sim1 
    case refl => constructor 
                 case h => constructor 
                           case left => constructor
                           case right => assumption        
    case step a b c ss _ h => cases (sim_step _ _ ss _ sim1)
                              case intro w q => cases q
                                                case intro rs2 simb => cases (h _ simb)
                                                                       case intro w' H => cases H  
                                                                                          exists w'
                                                                                          constructor
                                                                                          apply RTrans
                                                                                          assumption
                                                                                          assumption
                                                                                          assumption



                                               



-- part 9
/- PROBLEM 6: The final result!

  While this is the actual result that we care about: that if 
  a term runs to a boolean, then the term in compiles to runs to the compiled version of that boolean, it is actually one of the easier proofs, as most of the work is done by the theorems above. 

  If you are wondering, why running to a boolean? If our program 
  runs forever, there isn't much we can say about the target (we could 
  say we want it to run forever, but we often don't). The only other
  value it could run to is a function (lam). But knowing how to equate 
  lambdas is tricky (as they contain code, and equivalence of code sort 
  of requires running, which is circular). Fortunately, it turns out 
  that by showing equivalence of booleans, we essentially get 
  equivalence of functions, as if we have a term `t` that should run to 
  a function (say, of a single boolean argument), then our theorem, 
  since it holds of @italic{all} expressions, will
  tell us that both `t true` and `t false` will run to the same thing.
-/
-- part 10

-- 7 lines
theorem correct : forall t b, Rstar SStep t (Source.b b) ->
                              Rstar TStep t.compile ((Source.b b).compile) := 
 by intros e n rst1
    cases (step_sim_star _ _ rst1 _ (compile_sim e))
    case intro w H =>
      cases H
      case intro H1 H2 =>
        cases H2
        assumption
                                                                

    
                  
-- part 10
