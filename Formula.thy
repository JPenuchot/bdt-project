theory Formula
imports BDT 
begin

type_synonym atom = bool

datatype binop = And | Or | Impl

(* inductive definition of abstract syntax trees for formula *)

datatype form = 
     Var  "var" 
   | Atom "atom"
   | Neg  "form"
   | Bin  "binop" "form" "form"


text \<open> Notations \<close>

syntax        "_top"  :: "form"   ("top\<^sub>F")
translations  "top\<^sub>F"  == "(CONST Atom) (CONST True)"

syntax        "_bot"  :: "form"   ("bot\<^sub>F")
translations  "bot\<^sub>F"  == "(CONST Atom) (CONST False)"

syntax        "_neg"  :: "form \<Rightarrow> form"   ("neg\<^sub>F _")
translations  "neg\<^sub>F F" == "(CONST Neg) F"

syntax        "_and"  :: "form \<Rightarrow> form \<Rightarrow> form"   ("and\<^sub>F _ _")
translations  "and\<^sub>F F1 F2" == "(CONST Bin) (CONST And) F1 F2"

syntax        "_or"  :: "form \<Rightarrow> form \<Rightarrow> form"   ("or\<^sub>F _ _")
translations  "or\<^sub>F F1 F2" == "(CONST Bin) (CONST Or) F1 F2"

syntax        "_impl"  :: "form \<Rightarrow> form \<Rightarrow> form"   ("impl\<^sub>F _ _")
translations  "impl\<^sub>F F1 F2" == "(CONST Bin) (CONST Impl) F1 F2"

(** Test cases *)

definition p0 where "p0 = Var 0"
definition p1 where "p1 = Var 1"
definition p2 where "p2 = Var 2"

definition P0     where "P0        = impl\<^sub>F p0 p1"
definition P1     where "P1        = impl\<^sub>F p1 P0"
definition dnegp  where "dnegp P Q = (impl\<^sub>F (impl\<^sub>F P Q) Q)"
definition P2     where "P2        = dnegp P0 p0"

(** ** Semantic *)
(* Boolean interpretation of binary operators *)

fun interp ("I\<^sub>f\<^sub>o\<^sub>r\<^sub>m") where
    "I\<^sub>f\<^sub>o\<^sub>r\<^sub>m  _ _ = undefined" (* a completer *)
 
value "I\<^sub>f\<^sub>o\<^sub>r\<^sub>m P2 Itrue "
value "I\<^sub>f\<^sub>o\<^sub>r\<^sub>m P2 Ifalse "
value "I\<^sub>f\<^sub>o\<^sub>r\<^sub>m P2 (list2interpretation [True,False] False) "
value "I\<^sub>f\<^sub>o\<^sub>r\<^sub>m P2 (list2interpretation [False,True] False) "

(** ** Equivalence *)

definition equiv where "equiv P Q = (\<forall>I. I\<^sub>f\<^sub>o\<^sub>r\<^sub>m  P I = I\<^sub>f\<^sub>o\<^sub>r\<^sub>m  Q I)"

lemma negimpl : "equiv (neg\<^sub>F (impl\<^sub>F P Q)) (and\<^sub>F P (neg\<^sub>F Q))"
unfolding equiv_def
by auto



lemma implor : "equiv (impl\<^sub>F P Q) (or\<^sub>F (neg\<^sub>F P)  Q)" 
unfolding equiv_def
by auto


(** ** Validity *)
definition valid where "valid P = (\<forall> I. I\<^sub>f\<^sub>o\<^sub>r\<^sub>m  P I = True)"

lemma Pierce :" valid (impl\<^sub>F (impl\<^sub>F (impl\<^sub>F P Q) P) P)"
unfolding valid_def
by auto

end
