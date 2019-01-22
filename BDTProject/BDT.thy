chapter\<open>The Theory of Binary Decision Trees (BDT) \<close>

theory   BDT
imports  Main
begin

type_synonym var = nat

type_synonym "interpretation" = "var \<Rightarrow> bool"     


fun    list2interpretation :: "'a list \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a"
where "list2interpretation [] d = (\<lambda> x. d)"
     |"list2interpretation (a # m) d = (\<lambda> x. case x of 
                                     0 \<Rightarrow> a 
                                   | Suc n \<Rightarrow>  list2interpretation m d n )"

(* definition  interpl where "interpl l = list2interpretation l True" *)
definition  Ifalse ("I\<^sub>\<bottom>") where "I\<^sub>\<bottom>  = (\<lambda> x::nat . False)" 
definition  Itrue  ("I\<^sub>\<top>") where "I\<^sub>\<top>  = (\<lambda> x::nat . True)"

section\<open>Basic structures and notations\<close>

type_synonym atom = bool

datatype     bdt  = Atom  atom  | IF  var bdt bdt

text \<open> Notations \<close>

syntax        "_topt"  :: "bdt"   ("topt")
translations  "topt" == "(CONST Atom) (CONST True)"

syntax        "_bott"        :: "bdt"   ("bott")
translations  "bott" == "(CONST Atom) (CONST False)"

definition    var   where "var n = IF n topt bott"


subsection \<open> Semantics \<close>

fun "interpret":: "bdt \<Rightarrow> interpretation \<Rightarrow>  bool" ("I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>_\<rbrakk> _")
where "I\<^sub>b\<^sub>d\<^sub>t\<lbrakk>Atom a\<rbrakk> \<gamma> = a"
     |"I\<^sub>b\<^sub>d\<^sub>t\<lbrakk>IF x P Q\<rbrakk> \<gamma> = (if \<gamma> x then I\<^sub>b\<^sub>d\<^sub>t\<lbrakk>P\<rbrakk>\<gamma> else I\<^sub>b\<^sub>d\<^sub>t\<lbrakk>Q\<rbrakk>\<gamma>)"

(** tests *)
thm BDT.interpret.simps

definition Pt where "Pt \<equiv> (IF (0::nat) (IF 1 topt topt) (IF 1 topt topt))"

value "I\<^sub>\<bottom>"

value "I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>Pt\<rbrakk>  I\<^sub>\<bottom> "
value "I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>Pt\<rbrakk> I\<^sub>\<bottom>"
value "(I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>Pt\<rbrakk> (list2interpretation [True,False] True) )"
value "(I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>Pt\<rbrakk> (list2interpretation [False,True] False) )"

(* Trivial equality to be used for rewriting *)

lemma interpret_If :  "interpret  (IF x P Q) I =   (if I x then interpret P I 
                                                           else interpret Q I)" 
  by simp

lemma interpret_true [simp]: 
  "I x \<Longrightarrow> interpret (IF x P Q) I  = interpret P I " by simp

lemma interpret_false [simp]: 
  "\<not>I x \<Longrightarrow> interpret (IF x P Q) I = interpret Q I " by simp

section\<open> Logical operations on BDT \<close>

fun    neg :: "bdt \<Rightarrow> bdt"
where "neg (Atom a) =  Atom (\<not> a)"
     |"neg (IF x l r) = IF x (neg l) (neg r)"


find_theorems name:BDT.neg

lemma negt_corr : "I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>neg P\<rbrakk> I = (\<not> I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>P\<rbrakk> I)"
  apply(rule BDT.neg.induct)
  by auto

section\<open>BinaryCombination.\<close>

fun comb where
    comb_a_a  :"comb opn (Atom a) (Atom b)  = Atom (opn a b)"
   |comb_a_if :"comb opn (Atom a) (IF x l r) = IF x (comb opn (Atom a) l) (comb opn (Atom a) r)"
   |comb_if_a :"comb opn (IF x l r) (Atom b) = IF x (comb opn l (Atom b)) (comb opn r (Atom b))"
   |comb_if_if:"comb opn (IF x l r) (IF y l' r') = 
                  (if x < y then  IF x (comb opn l (IF y l' r')) (comb opn r (IF y l' r'))
                            else if y < x then IF y (comb opn (IF x l r) l')(comb opn (IF x l r) r')
                                          else IF x (comb opn l l') (comb opn r r'))"
find_theorems name:comb

definition opn where "opn x y \<equiv> x \<or> y"

value "comb opn (Atom True) (Atom False)" 


(*
Comparison with Coq: the following intuitive definition is not directly accepted 
Fixpoint bint (t u: bdt) : bdt := 
  match t with 
     Atomt a =>  match u with Atomt b => Atomt (op a b) 
                           |  IFt x l r => IFt x (bint t l) (bint t r)
                 end
   | IFt x l r => match u with Atomt b => IFt x (bint l u) (bint r u) 
                             |  IFt y l' r' => match nat_compare x y with 
                                 Lt => IFt x (bint l u) (bint r u) 
                                |Eq => IFt x (bint l l') (bint r r') 
                                |Gt => IFt y (bint t l') (bint t r') end
                  end
  end.
*)

(* This works in Isabelle without splitting in two fixpoints.  *)


lemma comb_eq : "comb opn (IF x l r) (IF x l' r') = (IF x (comb opn l l') (comb opn r r'))"
  by(clarsimp)

lemma comb_le : "x < y \<Longrightarrow> comb opn (IF x l r) (IF y l' r') 
                           = (IF x (comb opn l (IF y l' r')) (comb opn r (IF y l' r')))"
  by(simp)

lemma comb_ge : "y < x \<Longrightarrow> comb opn (IF x l r) (IF y l' r')
                           = IF y (comb opn (IF x l r) l') (comb opn (IF x l r) r')"
  by(simp)


(** Instantiation on standard boolean operations *)
definition "and"  where "and  = comb (\<and>)"
definition or     where "or   = comb (\<or>)"
definition impl   where "impl = comb (\<longrightarrow>)"


(** formula examples *)

definition p0   where "p0       = var 0"
definition p1   where "p1       = var 1"
definition P0   where "P0       = impl p0 p1"
definition P1   where "P1       = impl p1 P0"
definition dneg where "dneg P Q = impl (impl P Q) Q"
definition P2   where "P2       = dneg P0 p0"

value "P1"
value "P2"

(* examples for complicated proofs involving nested inductions ... *)
lemma comb_correct : "(I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>comb f P Q\<rbrakk> \<gamma>) = f (I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>P\<rbrakk> \<gamma>) (I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>Q\<rbrakk> \<gamma>)"
apply(rule_tac x=Q in spec)
apply(induct_tac P)
 apply(rule allI, rename_tac x Q, induct_tac Q)
 apply simp_all
apply(rename_tac "v" "x2" "x3")
apply(case_tac "\<gamma> v", simp_all)
 apply(rule allI)
 apply(rename_tac "v" "x2" "x3" "Q") 
 apply(induct_tac Q)
  apply simp_all
 apply blast
apply(rule allI)
apply(rename_tac "v" "x2" "x3" "Q") 
apply(induct_tac Q)
 apply simp_all
by blast

text\<open> ... and the same as structured proof \<close>

lemma comb_correct' : "(I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>comb f P Q\<rbrakk> I) = f (I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>P\<rbrakk> I) (I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>Q\<rbrakk> I)"
proof(induct P arbitrary: Q)
   case (Atom a) show ?case by(induct_tac Q, simp_all)
next
   fix v::nat fix P1 P2 Q
   assume hyp1 : "\<And>Q. interpret (comb f P1 Q) I  = f (interpret P1 I) (interpret Q I)"
   and    hyp2 : "\<And>Q. interpret (comb f P2 Q) I  = f (interpret P2 I) (interpret Q I)"
   show "interpret (comb f (IF v P1 P2) Q) I = f (interpret (IF v P1 P2) I ) (interpret Q I )"
        (is "?lhs = ?rhs")
     txt\<open>this is a pattern-matching against the above ``show'' defining @{term "?lhs"} \<close>
      apply simp 
      proof(cases "I v", simp_all) txt\<open> you might try here @{command print_cases} to check the
                                        environment of local assumptions here ... \<close>
         case True show "?lhs = f (interpret P1 I ) (interpret Q I)"
            txt \<open> the fact @{thm True} is here just a name for the assumption @{term "I v"} \<close>
            apply(induct Q) 
            apply(simp_all add: hyp1 hyp2 True)  
            using True by blast
      next 
         case False show "?lhs = f (interpret P2 I ) (interpret Q I)"
            apply(induct Q) 
            apply(simp_all add: hyp1 hyp2 False)  
            using False by blast            
      qed
qed 
text\<open> The advantages of this format are:
      \<^enum> proof and sub-proof structures were made explicit; 
        if one sub-proof breaks during development, the other 
        sub-proofs may still be valid. Structured proofs are therefore
        more stable under development as apply-style proofs, allow for a
        faster impact-analysis under change and
        can be evaluated in parallel --- the user profits even in short-term.
      \<^enum> The Isabelle community therefore encourages structured proofs.
      \<^enum> Major recurring proof patterns (induction with generalization,
        case-distinctions etc.) were made explicit which makes this
        proof format readable even for non-Isabelle users. (Well, sort of...)
      \<^enum> The notational burden to re-declare (abstractions of) the current proof state
        when entering a sub-proof can be alleviated by using case-notation and
        patterns from previous re-declarations. Note that the order of re-declaration
        is arbitrary. 
\<close>


lemma or_correct   : "I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>or P Q\<rbrakk> \<gamma> = (I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>P\<rbrakk> \<gamma>  \<or> I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>Q\<rbrakk> \<gamma>)"
by (simp add: BDT.or_def comb_correct)

lemma and_correct  : "I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>and P Q\<rbrakk> \<gamma>  = (I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>P\<rbrakk> \<gamma>  \<and> I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>Q\<rbrakk> \<gamma> )"
by (simp add: BDT.and_def comb_correct)

lemma impl_correct : "I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>impl P Q\<rbrakk> \<gamma>  = (I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>P\<rbrakk> \<gamma>  \<longrightarrow> I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>Q\<rbrakk> \<gamma> )"
by (simp add: BDT.impl_def comb_correct)


primrec    exist\<^sub>v\<^sub>a\<^sub>r :: "var \<Rightarrow> bdt \<Rightarrow> bdt"
where     "exist\<^sub>v\<^sub>a\<^sub>r x (Atom a) = (Atom a)" (* x does not occur in t *)
         |"exist\<^sub>v\<^sub>a\<^sub>r x (IF y l r) = (if x < y then (IF y l r) (* x does not occur in t *) 
                                            else if y > x then IF y (exist\<^sub>v\<^sub>a\<^sub>r x l) (exist\<^sub>v\<^sub>a\<^sub>r x r)
                                                          else or l r)"

text\<open>Hint: ``fun'' does not work here (at least not without providing a non-trivial termination
     ordering) since it chooses the lexicographic ordering as default ... \<close>

(** ordered n i t : all variables x in t are increasing on branches and i <= x < n *)
 
(* a completer: *)
inductive ordered :: "nat \<Rightarrow> nat \<Rightarrow> bdt \<Rightarrow> bool"
where     Oatom : "ordered x y (Atom a)"
         |Oif   : "i \<le> x \<and> x < n 
                   \<Longrightarrow> ordered n x l
                   \<Longrightarrow> ordered n x r
                   \<Longrightarrow> ordered n i (IF x l r)"

(* or alternative: *)

fun ordered' :: "nat \<Rightarrow> nat \<Rightarrow> bdt \<Rightarrow> bool"
  where  "ordered' x y (Atom a) = True"
        |"ordered' n i (IF x l r) = (if i \<le> x \<and> x < n
                                      then ordered' n x l \<and> ordered' n x r
                                      else False)"

(* for fun *)
fun     fv :: "bdt \<Rightarrow> nat set" 
where  "fv (Atom a) = {}"
      |"fv (IF x l r) = {x} \<union> fv l \<union> fv r"

lemma fv_neg : "fv(neg t) = fv t"
proof(induct t)
case (Atom x)
then show ?case by simp
next
  case (IF x1a t1 t2)
  then show ?case  by simp
qed

(* for fun *)
lemma fv_comb[simp]: "fv(comb f l r) = fv l \<union> fv r"
proof(induct l arbitrary: r)
  case (Atom x)
  then show ?case 
     proof(induct r)
       case (Atom x)
       then show ?case by simp 
     next
       case (IF x1a r1 r2)
       then show ?case by simp 
     qed 
next
  case (IF x1a l1 l2)
  then show ?case   
     proof(induct r)
       case (Atom x)
       then show ?case by simp 
     next
       case (IF x1b r1 r2)
       then show ?case 
            apply(cases "x1a < x1b") apply simp apply blast
            apply(cases "x1b < x1a", simp_all) 
            apply(simp add: Un_left_commute inf_sup_aci(6) insert_commute)
            by blast
     qed
   qed

find_theorems name:BDT
find_theorems name:BDT.neg
find_theorems name:BDT.ordered

lemma neg_ordered_inv : "ordered n i P \<Longrightarrow> ordered n i (neg P)"
  apply(rule neg.induct)
  apply(simp add: Oatom)
  apply(rule Oif)
  
  sorry

  

lemma XXX : "ordered n x l \<Longrightarrow> ordered n x (comb f l (Atom a))"
  apply(rule neg.induct)
   apply(simp add : Oatom)
  find_theorems "ordered"
  sorry


lemma XXX' : "ordered n x r \<Longrightarrow> ordered n x (comb f (Atom a) r)"
  sorry

lemma "ordered n i P \<Longrightarrow> ordered n i Q \<Longrightarrow> ordered n i (comb f P Q)"
  sorry
  (* difficult nested induction; one has to provide useful non-obvious geeralizations. *)


lemma "ordered n i t \<Longrightarrow> (x < i \<or> n <= x) \<Longrightarrow>  I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>t\<rbrakk> (I(x:= b)) = I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>t\<rbrakk> I" 
  sorry
(* a completer ; main structure: induction over ordered_ness or t. *)

lemma exists_correct : 
"ordered n i t \<Longrightarrow> interpret (exist\<^sub>v\<^sub>a\<^sub>r x t) I 
                   = ( (interpret  t ( I(x := True)) \<or> (interpret t ( I(x:= False)) )) )"
  sorry



(** * Using BDT to encode sets of states and do symbolic model-checking *)

(** We start from a (finite) problem where states depend on a set of boolean variables x0..x(n-1) 
    Each state is represented as a formula over these variables corresponding to a bdt ordered between 
    0 and n.
    Each set of states can also be represented by a formula over the same variables 
    (takes the disjunction of all sets)

    The transition system is represented by a formula with 2n variables corresponding to the values 
    before (x_i) and after (x_(n+i)). 
       - A single transition between state Gi(x_0,..,x_(n-1)) and Gj(x_0,..,x_(n-1))
    becomes a formula T_(ij)(x_0,..,x_(2n-1))=G1(x_0,..,x_(n-1))/\G2(x_n,..,x_(2n-1))
    The transition system is a formula T(x_0,..,x_(2n-1))
    corresponding to the disjonction of all transitions.

    We can now compute a set of states leading to a set of situations R in k or less steps
        R_0=R
        R_(i+1)(x_0,..x_(n-1)) = 
          R_i(x_0,..x_(n-1))\/exists xn,..,x_(2n-1), T(x_0,..,x_(2n-1))/\R_i(x_n,..x_(2n-1))
    We will reach a fixpoint after a finite number of steps that is a solution of our problems.

    Of course the efficiency of this method depends on a more efficient representation of bdt 
    using reduced bdd,  sharing mechanisms and computation with memoization.
*) 

end
