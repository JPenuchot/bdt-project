(*  Title:      HOL/Lex/NA.thy
    ID:         $Id: NA.thy,v 1.1.1.1 2000/07/26 13:34:11 bu Exp $
    Author:     Tobias Nipkow
    Copyright   1998 TUM

Some basic definitions on automata.
*)

theory Automata
imports  Main 
begin

section{* The Type of Non-Deterministic Automata *}


find_theorems name:"na" name:"Automata"

record ('a,'s)na =
   start :: "'s"
   "next":: "'a \<Rightarrow> 's \<Rightarrow> 's set"
   fin   :: "('s \<Rightarrow> bool)"

find_theorems name:"na" name:"Automata" (* just to check the global effect of the record *)

(*create a set who have all the element of 'a list*)
text{* set of states reachable after a word  @{term "w"} from the initial state.*}
primrec delta :: "('a,'s)na \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> 's set"
where  "delta A []    p = {p}"                       (*return the set {p}*)
      |"delta A (a#w) p = \<Union>(delta A w ` next A a p)"(*next A a p return a*)


definition accepts ::   "('a,'s)na \<Rightarrow> 'a list \<Rightarrow> bool"
where     "accepts A w == \<exists> q \<in> delta A w (start A). fin A q"

definition step :: "('a,'s)na \<Rightarrow> 'a \<Rightarrow> ('s * 's)set"
where     "step A a == {(p,q) . q : next A a p}"


primrec steps :: "('a,'s)na \<Rightarrow> 'a list \<Rightarrow> ('s * 's)set"
where
 "steps A [] = Id"
|"steps A (a#w) =  step A a  O  steps A w "


lemma steps_append[simp] : "steps A (v @ w) =  steps A v O steps A w "
apply (induct "v" )
apply (simp_all add: O_assoc)
done

lemma in_steps_append [intro] :  "((p, r) \<in> steps A (v @ w)) = ((p, r) \<in> steps A v  O  steps A w)"
by(rule steps_append[THEN equalityE]) blast

lemma delta_conv_steps :  " \<forall>p. delta A w p = {q. (p, q) \<in> steps A w}"
  apply(induct w)
   apply(auto)
  using step_def apply fastforce
  using step_def by fastforce

lemma accepts_conv_steps : "accepts A w = (\<exists>q. (start A, q) \<in> steps A w \<and> fin A q)"
  by (simp add: accepts_def delta_conv_steps)



section{* Deterministic Automaton *}

record ('a,'s)da =
   start :: "'s"
   "next":: "'a \<Rightarrow> 's \<Rightarrow> 's"
   fin   :: "('s \<Rightarrow> bool)"


definition   foldl2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b"
where       "foldl2 f xs a == foldl (\<lambda>a b. f b a) a xs"

definition   delta\<^sub>d\<^sub>a :: "('a,'s)da \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> 's"
where       "delta\<^sub>d\<^sub>a A == foldl2 (da.next  A)"

definition   accepts\<^sub>d\<^sub>a ::  "('a,'s)da \<Rightarrow> 'a list \<Rightarrow> bool"
where       "accepts\<^sub>d\<^sub>a A == \<lambda>w. fin A (delta\<^sub>d\<^sub>a A w (start A))"


end