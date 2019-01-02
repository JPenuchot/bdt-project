theory PLProver
imports Main BDT Formula
begin


fun    form2bdt :: "form \<Rightarrow> bdt"
where "form2bdt (Atom a)= (BDT.Atom a)" 
     |"form2bdt (Var x) = (IF x (BDT.Atom True) (BDT.Atom False))" 
     |"form2bdt (Neg p) = (neg (form2bdt p) )" 
     |"form2bdt (Bin And p q)= comb (\<and>) (form2bdt p) (form2bdt q)" 
     |"form2bdt (Bin Or p q)= comb (\<or>) (form2bdt p) (form2bdt q)" 
     |"form2bdt (Bin Impl p q)= comb (\<longrightarrow>) (form2bdt p) (form2bdt q)" 
  
      

(** Tester la fonction *)
value "form2bdt P1"
value "form2bdt P2"

(** Prouver que la transformation form2bdt préserve la sémantique des formules *)

lemma form2bdt_correct:" I\<^sub>f\<^sub>o\<^sub>r\<^sub>m  \<phi> \<gamma> = I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>form2bdt \<phi>\<rbrakk> \<gamma>"
proof(induct \<phi>)
  case (Var x)
  then show ?case   by simp
next
  case (Atom x)
  then show ?case  by simp
next
  case (Neg \<phi>)
  then show ?case 
    by(simp add:negt_corr)
next
  case (Bin binop \<phi>1 \<phi>2)
  then show ?case
    proof(cases binop)
      case And
      show ?thesis by(simp add: `I\<^sub>f\<^sub>o\<^sub>r\<^sub>m \<phi>1 \<gamma> = I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>form2bdt \<phi>1\<rbrakk> \<gamma>` 
                                `I\<^sub>f\<^sub>o\<^sub>r\<^sub>m \<phi>2 \<gamma> = I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>form2bdt \<phi>2\<rbrakk> \<gamma>` 
                                `binop = And` comb_correct)
    next
      case Or
        assume * : "I\<^sub>f\<^sub>o\<^sub>r\<^sub>m \<phi>1 \<gamma> = I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>form2bdt \<phi>1\<rbrakk> \<gamma>"
        and ** : "I\<^sub>f\<^sub>o\<^sub>r\<^sub>m \<phi>2 \<gamma> = I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>form2bdt \<phi>2\<rbrakk> \<gamma>"
        and ***: " binop = Or"
      then show ?thesis by(simp add: * ** *** comb_correct)
    next
      case Impl
        assume * : "I\<^sub>f\<^sub>o\<^sub>r\<^sub>m \<phi>1 \<gamma> = I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>form2bdt \<phi>1\<rbrakk> \<gamma>"
        and ** : "I\<^sub>f\<^sub>o\<^sub>r\<^sub>m \<phi>2 \<gamma> = I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>form2bdt \<phi>2\<rbrakk> \<gamma>"
        and ***: " binop = Impl"
      then show ?thesis by(simp add: * ** *** comb_correct)
    qed
qed   
  
  
  
  
  
  
  
lemma form2bdt_correct':" I\<^sub>f\<^sub>o\<^sub>r\<^sub>m  \<phi> \<gamma> = I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>form2bdt \<phi>\<rbrakk> \<gamma>"  
proof(induct \<phi>)
  case (Var x)
  then show ?case by simp
next
  case (Atom x)
  then show ?case by simp
next
  case (Neg \<phi>)
  then show ?case 
       proof(simp,cases \<phi>)
         case (Var x1)
         then show "\<lbrakk>I\<^sub>f\<^sub>o\<^sub>r\<^sub>m \<phi> \<gamma> = I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>form2bdt \<phi>\<rbrakk> \<gamma>; \<phi> = Var x1\<rbrakk> \<Longrightarrow> (\<not> I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>form2bdt \<phi>\<rbrakk> \<gamma>) = 
                    I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>neg (form2bdt \<phi>)\<rbrakk> \<gamma>"
           by simp
       next
         case (Atom x2)
         then show " \<lbrakk>I\<^sub>f\<^sub>o\<^sub>r\<^sub>m \<phi> \<gamma> = I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>form2bdt \<phi>\<rbrakk> \<gamma>; \<phi> = form.Atom x2\<rbrakk> \<Longrightarrow> 
                     (\<not> I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>form2bdt \<phi>\<rbrakk> \<gamma>) = I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>neg (form2bdt \<phi>)\<rbrakk> \<gamma>" by simp
       next
         case (Neg x3)
         then show "\<lbrakk>I\<^sub>f\<^sub>o\<^sub>r\<^sub>m \<phi> \<gamma> = I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>form2bdt \<phi>\<rbrakk> \<gamma>; \<phi> = neg\<^sub>F x3\<rbrakk> \<Longrightarrow> 
                    (\<not> I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>form2bdt \<phi>\<rbrakk> \<gamma>) = I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>neg (form2bdt \<phi>)\<rbrakk> \<gamma>"     
             by (simp add: negt_corr')
       next
         case (Bin x41 x42 x43)
         then show "\<lbrakk>I\<^sub>f\<^sub>o\<^sub>r\<^sub>m \<phi> \<gamma> = I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>form2bdt \<phi>\<rbrakk> \<gamma>; \<phi> = Bin x41 x42 x43\<rbrakk> \<Longrightarrow> 
                    (\<not> I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>form2bdt \<phi>\<rbrakk> \<gamma>) = I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>neg (form2bdt \<phi>)\<rbrakk> \<gamma>"
           by (simp add: negt_corr')
       qed
next
  case (Bin binop \<phi>1 \<phi>2)
  then show ?case 
     apply(insert Bin.hyps)
     proof(cases binop)
       case And
       then show "\<lbrakk>I\<^sub>f\<^sub>o\<^sub>r\<^sub>m \<phi>1 \<gamma> = I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>form2bdt \<phi>1\<rbrakk> \<gamma>; 
                   I\<^sub>f\<^sub>o\<^sub>r\<^sub>m \<phi>2 \<gamma> = I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>form2bdt \<phi>2\<rbrakk> \<gamma>; binop = And\<rbrakk>
                   \<Longrightarrow> I\<^sub>f\<^sub>o\<^sub>r\<^sub>m (Bin binop \<phi>1 \<phi>2) \<gamma> = I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>form2bdt (Bin binop \<phi>1 \<phi>2)\<rbrakk> \<gamma>" 
             by(simp add:  comb_correct')
     next
       case Or
       then show "\<lbrakk>I\<^sub>f\<^sub>o\<^sub>r\<^sub>m \<phi>1 \<gamma> = I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>form2bdt \<phi>1\<rbrakk> \<gamma>; 
                   I\<^sub>f\<^sub>o\<^sub>r\<^sub>m \<phi>2 \<gamma> = I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>form2bdt \<phi>2\<rbrakk> \<gamma>; binop = Or\<rbrakk>
                   \<Longrightarrow> I\<^sub>f\<^sub>o\<^sub>r\<^sub>m (Bin binop \<phi>1 \<phi>2) \<gamma> = I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>form2bdt (Bin binop \<phi>1 \<phi>2)\<rbrakk> \<gamma>"
                      by(simp add:  comb_correct')
     next
       case Impl
       then show "\<lbrakk>I\<^sub>f\<^sub>o\<^sub>r\<^sub>m \<phi>1 \<gamma> = I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>form2bdt \<phi>1\<rbrakk> \<gamma>; 
                   I\<^sub>f\<^sub>o\<^sub>r\<^sub>m \<phi>2 \<gamma> = I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>form2bdt \<phi>2\<rbrakk> \<gamma>; binop = Impl\<rbrakk>
                   \<Longrightarrow> I\<^sub>f\<^sub>o\<^sub>r\<^sub>m (Bin binop \<phi>1 \<phi>2) \<gamma> = I\<^sub>b\<^sub>d\<^sub>t \<lbrakk>form2bdt (Bin binop \<phi>1 \<phi>2)\<rbrakk> \<gamma>" 
                      by(simp add:  comb_correct')
     qed     
qed


(** A quelle condition sur i j n m a-t-on ordered n i t -> ordered m j t ?
    faire la preuve correspondante *)

lemma ordered_incl: " ordered n i t \<Longrightarrow> \<forall> m j. undefined (* compléter *) \<Longrightarrow> ordered m j t"
sorry
(* compléter *)


(** Définir une fonction qui renvoie le maximum des variables 
   rencontrées dans une formule propositionnelle +1 (0 si pas de variable) 
   on pourra utiliser la fonction max *)

fun  maxvar 
where "maxvar (Atom a) = undefined "    (* compléter *)
     |"maxvar(Var x) =   undefined " (* compléter *)
     |"maxvar(Neg p) =  undefined " (* compléter *)
     |"maxvar(Bin opn p q) =  undefined " (* compléter *)
  

(** Prouver que le résultat de form2bdt donne un arbre ordonné entre 0 et maxvar *)

lemma form2bdt_ord :"ordered (maxvar f) 0 (form2bdt f)"
sorry
(* compléter *)


(** * Tester qu'un BDT (ordonné) est une tautologie *)
(* Ecrire une fonction booléenne qui teste si un BDT correspond à une tautologie *)

fun istauto 
where "istauto (BDT.Atom a) = undefined"  (* compléter *) 
     |"istauto (BDT.IF x l r) =  undefined"   (* compléter *) 

(** Enoncer et prouver la correction de ce test, on pourra distinguer 
    le cas où le test est positif et le cas où le test est négatif *)

lemma istauto_true_corr : "istauto t" 
      (* compléter *)
sorry



end
