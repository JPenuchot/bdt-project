theory RegExp2NAe
imports Main Automata RegExp 
begin

section {* NFA-epsilon automata as instance of non-deterministic automata *}
(*nae pour NFA-epsilon automata*)
type_synonym ('a,'s)nae = "('a option, 's) na"

syntax   (xsymbols)    "_eps" :: "('a,'s)nae \<Rightarrow> ('s * 's)set" ("eps")
translations           "eps A" == "(CONST step) A (CONST None)"

primrec steps\<^sub>n\<^sub>a\<^sub>e :: "('a,'s)nae \<Rightarrow> 'a list \<Rightarrow> ('s * 's)set"
where  "steps\<^sub>n\<^sub>a\<^sub>e A [] = (eps A)\<^sup>*"   (* eliminating stuttering steps via eps-closure *)
     | "steps\<^sub>n\<^sub>a\<^sub>e A (a#w) = (eps A)\<^sup>* O step A (Some a) O steps\<^sub>n\<^sub>a\<^sub>e A w " 
                                   (* Caution: lifts step over Some*)


lemma steps_epsclosure[simp] : "(eps A)\<^sup>* O steps\<^sub>n\<^sub>a\<^sub>e A w   = steps\<^sub>n\<^sub>a\<^sub>e A w"
  by (metis (no_types, lifting) O_assoc list.exhaust rtrancl_idemp_self_comp steps\<^sub>n\<^sub>a\<^sub>e.simps(1) steps\<^sub>n\<^sub>a\<^sub>e.simps(2))

lemma in_steps_epsclosure:"(p, q) \<in> (eps A)\<^sup>* \<Longrightarrow> (q, r) \<in>steps\<^sub>n\<^sub>a\<^sub>e A w \<Longrightarrow> (p, r) \<in> steps\<^sub>n\<^sub>a\<^sub>e A w"
  by (metis relcomp.relcompI steps_epsclosure)

lemma epsclosure_steps: " steps\<^sub>n\<^sub>a\<^sub>e A w  O (eps A)\<^sup>* = steps\<^sub>n\<^sub>a\<^sub>e A w"
  apply(induct w)
   apply simp
  by (simp add: O_assoc)

lemma in_epsclosure_steps : 
"(p, q) \<in> steps\<^sub>n\<^sub>a\<^sub>e A w \<Longrightarrow> (q, r) \<in> (eps A)\<^sup>* \<Longrightarrow> (p, r) \<in> steps\<^sub>n\<^sub>a\<^sub>e A w"
by(rule epsclosure_steps[THEN equalityE]) (blast)


lemma steps_append[simp] : "steps\<^sub>n\<^sub>a\<^sub>e A (v@w) =  steps\<^sub>n\<^sub>a\<^sub>e A v  O  steps\<^sub>n\<^sub>a\<^sub>e A w"
apply(induct_tac "v")
by (simp_all add:O_assoc) 

lemma in_steps_append[iff] : "((p, r) \<in> steps\<^sub>n\<^sub>a\<^sub>e A (v @ w)) = ((p, r) \<in> steps\<^sub>n\<^sub>a\<^sub>e A v O steps\<^sub>n\<^sub>a\<^sub>e A w) "
apply(rule epsclosure_steps[THEN equalityE])
by simp



definition accepts\<^sub>n\<^sub>a\<^sub>e :: "('a,'s)nae \<Rightarrow> 'a list \<Rightarrow> bool"
where     "accepts\<^sub>n\<^sub>a\<^sub>e A w \<equiv> \<exists>q. (na.start A, q) \<in> steps\<^sub>n\<^sub>a\<^sub>e A w \<and> na.fin A q"



text{* Now, we instantiate the class of non-deterministic automata with epsilon
       transitions one step further: nodes were represented by a bitvector.
       This paves the way for a particular attractive re-labelling scheme, where
       all node labels were just 'shifted' by prepending true or false;
       relabelling paves the way for automata-constructions where the name-spaces
       of node-labels must be kept disjoint. *}
type_synonym 'a bitsNAe = "('a ,bool list) nae"

syntax "_multipref"::"'a \<Rightarrow> 'a list set\<Rightarrow> 'a list set"(infixr "##" 65)
translations "x ## S"== "(#) x ` S"

value "True ## {[], [False], [True]}"

value " {[], [False], [True]}"

value "True##{}" 

value "(#) x `S"

definition atom :: "'a \<Rightarrow>'a bitsNAe"                                             
where "atom a ==\<lparr>na.start = [True],                                                  
                 na.next  = (\<lambda> b s. if s =[True] \<and> b = Some a then {[False]} else {}), 
                 na.fin   = (\<lambda> s. s = [False]) \<rparr>"                                        
               


definition union:: " 'a bitsNAe \<Rightarrow> 'a bitsNAe \<Rightarrow> 'a bitsNAe"
where "union l r == (let ql = na.start l;
                         dl = na.next l;
                         fl = na.fin l;
                         qr = na.start r;
                         dr = na.next r;
                         fr = na.fin r
                     in  \<lparr>na.start =[],                                                          
                          na.next = \<lambda>a s. case s of                                                    
                                            [] \<Rightarrow> if a=None
                                                  then {True#ql,False#qr}
                                                  else {}
                                           |left#s \<Rightarrow> if left
                                                      then True ## dl a s
                                                      else False ## dr a s,
              na.fin = \<lambda>s. case s of 
                      [] \<Rightarrow> False                                            
                      |left#s \<Rightarrow> if left then fl s else fr s\<rparr>) "


 
definition conc :: "'a bitsNAe \<Rightarrow> 'a bitsNAe \<Rightarrow> 'a bitsNAe"
where  "conc l r == (let ql = na.start l;
                         dl = na.next l;
                         fl = na.fin l;
                         qr = na.start r;
                         dr = na.next r;
                         fr = na.fin r
                     in  \<lparr>na.start = (True#ql),                                             
                          na.next = (\<lambda>a s. case s of                                            
                                             [] \<Rightarrow> {}
                                            |left#s \<Rightarrow> if left 
                                                       then (True ## dl a s)\<union>
                                                            (if fl s \<and> a =None then {False#qr}
                                                                               else{})
                                                       else False ## dr a s),
                          na.fin = (\<lambda>s. case s of 
                                             [] \<Rightarrow> False
                                            |left#s \<Rightarrow> \<not>left \<and> fr s) \<rparr>)  "                    



(*automate NFA-epsilon pour le constructeur Star*)
definition star :: " 'a bitsNAe \<Rightarrow> 'a bitsNAe"
where "star m == (let q = na.start m;
                      d = na.next m;
                      f = na.fin m
                  in \<lparr>na.start = [],                                                        
                      na.next =  \<lambda>a s.  case s of                                         
                                          []     \<Rightarrow> if a = None then {True#q} else {}
                                         |left#s \<Rightarrow> if left 
                                                    then (True ## d a s)\<union> 
                                                          (if f s \<and> a=None then {True#q} else {})
                                                    else {},
                     na.fin = \<lambda>s. case s of [] \<Rightarrow> True | left#s \<Rightarrow> left \<and> f s\<rparr>)"                                                               


(*en utiliser les définition precédante, rexp2nae traduite d'une expression régulière 
en un DFA-epsilon*)
primrec rexp2nae :: "'a rexp \<Rightarrow> 'a bitsNAe"
where  "rexp2nae Empty     = \<lparr>na.start = [], na.next = \<lambda>a s. {}, na.fin = \<lambda>s. False\<rparr>"
      |"rexp2nae(Atom a)   = atom a "
      |"rexp2nae(Alt r s)  = union (rexp2nae r) (rexp2nae s)"
      |"rexp2nae(Conc r s) = conc (rexp2nae r) (rexp2nae s)"
      |"rexp2nae(Star r)   = star(rexp2nae r)"




section  {* Basic properties on the automata construction *}

subsection{* atom *}

lemma fin_atom :"(na.fin (atom a) q) = (q = [False])"
by(simp add:atom_def)

lemma start_atom: "na.start (atom a) = [True]"
by(simp add:atom_def)

lemma eps_atom[simp]: "eps(atom a) = {}"
unfolding atom_def step_def
by auto


lemma in_step_atom_Some[simp]: "((p,q) \<in> step (atom a) (Some b)) = (p = [True] \<and> q = [False] \<and> b = a)"
by(simp add:atom_def step_def)



lemma False_False_in_steps_atom:  "([False],[False]) \<in> steps\<^sub>n\<^sub>a\<^sub>e (atom a) w = (w = [])"
proof (induct  "w") print_cases
   case Nil show ?case by simp
next
   case (Cons aa w) then show ?case by(auto simp: comp_def)
qed 


lemma start_fin_in_steps_atom : "((na.start (atom a), [False]) \<in> steps\<^sub>n\<^sub>a\<^sub>e (atom a) w) = (w = [a])"
proof (induct "w")
   case Nil show ?case by(simp add: start_atom) 
next 
   case (Cons a w) then show ?case apply(simp add: False_False_in_steps_atom comp_def start_atom)
                                   by (simp add: False_False_in_steps_atom relcomp.simps)
qed 

lemma accepts_atom : "accepts\<^sub>n\<^sub>a\<^sub>e (atom a) w = (w = [a])"
by(simp add: accepts\<^sub>n\<^sub>a\<^sub>e_def start_fin_in_steps_atom fin_atom)


subsection{* union *}

(***** lifting True/False over fin  *****)

lemma fin_union_True[rule_format,iff] :  " \<forall>L R. na.fin (union L R) (True # p) = na.fin L p"
unfolding union_def by simp


lemma fin_union_False[rule_format,iff] : "\<forall>L R. na.fin (union L R) (False # p) = na.fin R p"
unfolding union_def by (simp)


(***** lifting True/False over step *****)

lemma True_in_step_union[rule_format,iff] :
"\<forall>L R. ((True # p, q) \<in> step (union L R) a) = (\<exists>r. q = True # r \<and> (p, r) \<in> step L a)"
unfolding union_def step_def by (simp) (blast)


lemma False_in_step_union[rule_format,iff] :
" \<forall>L R. ((False # p, q) \<in> step (union L R) a) = (\<exists>r. q = False # r \<and> (p, r) \<in> step R a) "
unfolding union_def step_def by (simp)(blast)

(***** lifting True/False over epsclosure  *****)


lemma True_epsclosure_union [iff]: 
"((True # p, q) \<in> (eps (union l r))\<^sup>*) = (\<exists>p'. q = True # p' \<and> (p, p') \<in> (eps l)\<^sup>*) "
proof - 
  have * : "\<And> tp tq l r .(tp, tq) \<in> (eps (union l r))\<^sup>* \<Longrightarrow> 
                  \<forall>p. tp = True # p \<longrightarrow> (\<exists>q. (p, q) \<in> (eps l)\<^sup>* \<and> tq = True # q) "
           apply (erule rtrancl_induct )
            apply(blast) 
           by auto 
  have **: "\<And> p q l r. (p, q) \<in> (eps l)\<^sup>* \<Longrightarrow> (True # p, True # q) \<in> (eps (union l r))\<^sup>*"
           apply (erule rtrancl_induct )  
            apply (blast)
           by (meson True_in_step_union rtrancl.simps)
  show ?thesis
  by(blast dest : * **)
qed

lemma False_epsclosure_union [iff]: 
"((False # p, q) \<in> (eps (union l r))\<^sup>*) = (\<exists>p'. q = False # p' \<and> (p, p') \<in> (eps r)\<^sup>*) "
proof - 
  have * : "\<And> tp tq l r . (tp, tq) \<in> (eps (union l r))\<^sup>* \<Longrightarrow> 
                  \<forall>p. tp = False # p \<longrightarrow> (\<exists>q. (p, q) \<in> (eps r)\<^sup>* \<and> tq = False # q)"
           apply (erule rtrancl_induct )
            apply(blast) 
           by auto
  have **: "\<And> p q l r.(p, q) \<in> (eps r)\<^sup>* \<Longrightarrow> (False # p, False # q) \<in> (eps (union l r))\<^sup>*"
           apply (erule rtrancl_induct ) 
            apply (blast)
           by (meson False_in_step_union rtrancl.simps)
  show ?thesis
  by(blast dest : * **)
qed


(***** lifting True/False over steps  *****)

lemma lift_True_over_steps_union'':
 " \<forall>p. ((True # p, q) \<in> steps (union LL RR) w) = (\<exists>r. q = True # r \<and> (p, r) \<in> steps LL w)"
by (induct_tac "w") ( force+)



lemma lift_True_over_steps_union [rule_format,iff]:
 " \<forall>p. ((True # p, q) \<in> steps\<^sub>n\<^sub>a\<^sub>e (union l r) w) = (\<exists>p'. q = True # p' \<and> (p, p') \<in> steps\<^sub>n\<^sub>a\<^sub>e l w)"
by (induct_tac "w") ( force+)


lemma lift_False_over_steps_union[rule_format,iff]:
 "\<forall>p. ((False # p, q) \<in> steps\<^sub>n\<^sub>a\<^sub>e (union l r) w) =  (\<exists>p'. q = False # p' \<and> (p, p') \<in> steps\<^sub>n\<^sub>a\<^sub>e r w)"
by (induct_tac "w" ) (force+)


(***** Start state of the Epsilon hull  *****)

lemma unfold_rtrancl2 : "R\<^sup>* = Id \<union> R O R\<^sup>*"
apply (rule Set.set_eqI) 
apply(simp only: Product_Type.split_paired_all) (* by (split_all_tac 1); *)
apply (rule iffI)
 apply (erule rtrancl_induct)
  apply blast
 apply(blast intro: rtrancl_into_rtrancl)
by auto


lemma in_unfold_rtrancl2: "((p, q) \<in> R\<^sup>*) = (q = p \<or> (\<exists>r. (p, r) \<in> R \<and> (r, q) \<in> R\<^sup>*))"
apply(rule unfold_rtrancl2[THEN equalityE]) by blast


lemmas epsclosure_start_step_union [iff] = in_unfold_rtrancl2[of _ "na.start(union _ _)"]


lemma start_eps_union[iff]:
 "((na.start (union l r), q) \<in> eps (union l r)) = (q = True # na.start l \<or> q = False # na.start r)"
unfolding union_def step_def by simp


lemma not_start_step_union_Some:  "(na.start(union l r), q) \<notin> step (union l r) (Some a)"
unfolding union_def step_def by simp


lemma steps_union:
 "((na.start (union l r), q) \<in> steps\<^sub>n\<^sub>a\<^sub>e (union l r) w) =
    ((w = [] \<and> q = na.start (union l r)) \<or>
     (\<exists>p. q = True # p \<and> (na.start l, p) \<in> steps\<^sub>n\<^sub>a\<^sub>e l w \<or> 
          q = False # p \<and> (na.start r, p) \<in> steps\<^sub>n\<^sub>a\<^sub>e r w))"
proof(induct "w")
   case Nil show ?case
     apply(simp,subst unfold_rtrancl2)
     by blast+
next
  case (Cons a S) show ?case 
    apply(simp,subst unfold_rtrancl2) 
    
    apply(auto simp: not_start_step_union_Some relcomp.relcompI)
    by blast+
qed


lemma start_union_not_final[rule_format, iff]:
 "!L R. ~ na.fin (union L R) (na.start(union L R))"
unfolding union_def by (simp)


lemma accepts_union : "accepts\<^sub>n\<^sub>a\<^sub>e (union l r) w = (accepts\<^sub>n\<^sub>a\<^sub>e l w \<or> accepts\<^sub>n\<^sub>a\<^sub>e r w)"
unfolding accepts\<^sub>n\<^sub>a\<^sub>e_def
by(simp add: steps_union)(auto)

section{* conc *}

(** True/False in fin **)

lemma fin_conc_True[rule_format,iff]:
 "!L R. na.fin (conc L R) (True#p) = False"
unfolding conc_def by simp

lemma fin_conc_False[rule_format,iff]:
 "!L R. na.fin (conc L R) (False#p) = na.fin R p"
unfolding conc_def by simp

(** True/False in step **)

lemma True_step_conc [rule_format,iff]:
 " \<forall>L R. ((True # p, q) \<in> step (conc L R) a) =
          ((\<exists>r. q = True # r \<and> (p, r) \<in> step L a) \<or>
           na.fin L p \<and> a = None \<and> q = False # na.start R)"
unfolding conc_def step_def
by (simp) (blast)


lemma False_step_conc [rule_format,iff]:
 "\<forall>L R. ((False # p, q) \<in> step (conc L R) a) = (\<exists>r. q = False # r \<and> (p, r) \<in> step R a)"
unfolding conc_def step_def
by (simp, blast)

(** False in epsclosure **)

lemma False_epsclosure_conc [iff]:
     "((False # p, q) \<in> (eps (conc l r))\<^sup>*) = (\<exists>r'. q = False # r' \<and> (p, r') \<in> (eps r)\<^sup>*)"
     (is "?lhs = ?rhs")
proof(rule iffI)
     assume *: "?lhs"
     have  **: "\<And> tp tq. (tp, tq) \<in> (eps (conc l r))\<^sup>* \<Longrightarrow>
                    \<forall>p. tp = False # p \<longrightarrow> (\<exists>q. (p, q) \<in> (eps r)\<^sup>* \<and> tq = False # q)"
                    apply (erule rtrancl_induct)
                     apply (blast)
                    by(blast intro : rtrancl_into_rtrancl)
     show      "?rhs"  using * ** by(blast)
next 
     assume  *: "?rhs"
     have   **: "\<And>p q. (p, q) \<in> (eps r)\<^sup>* \<Longrightarrow> (False # p, False # q) \<in> (eps (conc l r))\<^sup>*"
                    apply (erule rtrancl_induct)
                     apply (blast)
                    by(blast intro: rtrancl_into_rtrancl)
     show       "?lhs" using * ** by(blast)
qed


lemma False_steps_conc[rule_format, iff]:
 "\<forall>p. ((False # p, q) \<in> steps\<^sub>n\<^sub>a\<^sub>e (conc l r) w) = 
      (\<exists>r'. q = False # r' \<and> (p, r') \<in> steps\<^sub>n\<^sub>a\<^sub>e r w)"
apply (induct "w" )
 apply (simp)
apply (simp)
by fast

(** True in epsclosure **)

lemma True_True_eps_concI :
 "(p, q) \<in> (eps l)\<^sup>* \<Longrightarrow> (True # p, True # q) \<in> (eps (conc l r))\<^sup>*"
apply (erule rtrancl_induct)
 apply blast
by (blast intro: rtrancl_into_rtrancl)

lemma True_True_steps_concI[rule_format]:
 "\<forall>p. (p, q) \<in> steps\<^sub>n\<^sub>a\<^sub>e l w \<longrightarrow> (True # p, True # q) \<in> steps\<^sub>n\<^sub>a\<^sub>e (conc l r) w"
apply (induct "w")
 apply (simp  add: True_True_eps_concI)
apply (simp)
by (blast intro: True_True_eps_concI)


(** True in epsclosure **)


lemma True_False_eps_concI : 
 "na.fin l p \<Longrightarrow> (True # p, False # na.start r) \<in> eps (conc l r)"
unfolding conc_def step_def by auto


lemma rtrancl_into_rtrancl2: "\<lbrakk>(a, b) \<in>  r; (b, c) \<in> r\<^sup>*\<rbrakk> \<Longrightarrow> (a, c) \<in> r\<^sup>*"
  by (auto intro: rtrancl_trans)


lemma True_epsclosure_conc[iff]:
 "((True # p, q) \<in> (eps (conc LL RR))\<^sup>*) =
    ((\<exists>r. (p, r) \<in> (eps LL)\<^sup>* \<and> q = True # r) \<or>
     (\<exists>r. (p, r) \<in> (eps LL)\<^sup>* \<and>
          na.fin LL r \<and> (\<exists>s. (na.start RR, s) \<in> (eps RR)\<^sup>* \<and> q = False # s)))"
  (is "?lhs = ?rhs")
proof (rule iffI)
  assume * : "?lhs"
  have  ** : "\<And> tp tq LL R.(tp, tq) \<in> (eps (conc LL R))\<^sup>* \<Longrightarrow>
                 \<forall>p. tp = True # p \<longrightarrow>
                     (\<exists>q. tq = True # q \<and> (p, q) \<in> (eps LL)\<^sup>*) \<or>
                     (\<exists>q r. tq = False # q \<and> (p, r) \<in> (eps LL)\<^sup>* 
                            \<and> na.fin LL r \<and> (na.start R, q) \<in> (eps R)\<^sup>*)"
             apply (erule rtrancl_induct)
              apply (blast)
             by (blast intro: rtrancl_into_rtrancl)
  show       "?rhs"
             using *  by (blast dest: **)
next
  assume * : "?rhs"
  have  ** : "\<And>p q L R. (p, q) \<in> eps R \<Longrightarrow> (False # p, False # q) \<in> eps (conc L R)"
             unfolding conc_def step_def by auto
  have ***:  "\<And> p q l r. (p, q) \<in> (eps r)\<^sup>* \<Longrightarrow> (False # p, False # q) \<in> (eps (conc l r))\<^sup>*"
               apply (erule rtrancl_induct)
                apply (blast)
               apply(drule **)
               by (blast intro : rtrancl_into_rtrancl)
  show       "?lhs"
             apply (insert *, erule disjE)
              apply (blast intro: True_True_eps_concI)
             apply(clarify)
             apply(rule rtrancl_trans)
             apply(erule True_True_eps_concI)
             apply(rule rtrancl_into_rtrancl2)
             apply(erule True_False_eps_concI)
             apply(erule ***)
             done
qed


lemma True_steps_concD [rule_format]:
 "\<forall>p. (True # p, q) \<in> steps\<^sub>n\<^sub>a\<^sub>e (conc l r) w \<longrightarrow>
        (\<exists>r'. (p, r') \<in> steps\<^sub>n\<^sub>a\<^sub>e l w \<and> q = True # r') \<or>
        (\<exists>u v. w = u @ v \<and>
               (\<exists>r'. (p, r') \<in> steps\<^sub>n\<^sub>a\<^sub>e l u \<and> na.fin l r' \<and> 
                     (\<exists>s. (na.start r, s) \<in> steps\<^sub>n\<^sub>a\<^sub>e r v \<and> q = False # s)))"
proof (induct "w") 
     case Nil show ?case  by (simp)
next
     case (Cons a w) then show ?case   (* TODO : RESTRUCTURE THIS *)
          apply (simp)
          apply (clarify del:disjCI)
          apply (erule disjE)
           apply (clarify del:disjCI)
           apply (erule disjE)
            apply (clarify del:disjCI)
            apply (erule allE, (erule notE | erule impE)+, assumption) 
            apply (erule disjE)
             apply (blast)
            apply (rule disjI2)
            apply (clarify)
            apply (simp)
            apply (rule_tac x="a#u" in exI)
            apply (simp)
            apply (blast)
           apply (blast)
          apply (rule disjI2)
          apply (clarify)
          apply simp 
          apply (rule_tac x="[]" in exI)
          apply (simp)
          apply (blast )
          done
qed

(** True in steps **)

lemma True_steps_conc:
 "((True # p, q) \<in> steps\<^sub>n\<^sub>a\<^sub>e (conc l r) w) =
    ((\<exists>r. (p, r) \<in> steps\<^sub>n\<^sub>a\<^sub>e l w \<and> q = True # r) \<or>
     (\<exists>u v. w = u @ v \<and>
            (\<exists>r'. (p, r') \<in> steps\<^sub>n\<^sub>a\<^sub>e l u \<and>
                 na.fin l r' \<and> (\<exists>s. (na.start r, s) \<in> steps\<^sub>n\<^sub>a\<^sub>e r v \<and> q = False # s))))"
by(blast dest: True_steps_concD intro: True_True_steps_concI in_steps_epsclosure)


(** starting from the start **)

lemma start_conc [rule_format]:
  " \<forall>L R. na.start (conc L R) = True # na.start L"
unfolding conc_def by (simp)


lemma final_conc [rule_format]:
  "!L R. na.fin(conc L R) p = (\<exists> s. p = False#s \<and> na.fin R s)"
unfolding conc_def by (simp  split: list.split)


lemma accepts_conc:
 "accepts\<^sub>n\<^sub>a\<^sub>e (conc l r) w = (\<exists> u v. w = u@v \<and> accepts\<^sub>n\<^sub>a\<^sub>e l u \<and> accepts\<^sub>n\<^sub>a\<^sub>e r v)"
by(simp add: accepts\<^sub>n\<^sub>a\<^sub>e_def True_steps_conc final_conc start_conc)(blast)

(******************************************************)
(*                       star                         *)
(******************************************************)

lemma True_in_eps_star [rule_format,iff]:
 "\<forall>A. ((True # p, q) \<in> eps (star A)) =
        ((\<exists>r. q = True # r \<and> (p, r) \<in> eps A) \<or> na.fin A p \<and> q = True # na.start A)"
unfolding star_def step_def
by (simp add:Let_def, blast)


lemma True_True_step_starI [rule_format]:
  "\<forall>A. (p, q) \<in> step A a \<longrightarrow> (True # p, True # q) \<in> step (star A) a "
unfolding star_def step_def by  (simp add: Let_def)


lemma True_True_eps_starI[rule_format] : 
  "(p, r) \<in> (eps A)\<^sup>* \<Longrightarrow> (True # p, True # r) \<in> (eps (star A))\<^sup>*"
proof (induct rule : rtrancl_induct) 
   case base show ?case by blast
next
   case step then show ?case by (blast intro: True_True_step_starI rtrancl_into_rtrancl) 
qed


lemma True_start_eps_starI [rule_format] :
 " \<forall>A. na.fin A p \<longrightarrow> (True # p, True # na.start A) \<in> eps (RegExp2NAe.star A) "
unfolding star_def step_def by(simp add: Let_def)

lemma result :
 "(tp, s) \<in> (eps (star A))\<^sup>* \<Longrightarrow>
    \<forall>p. tp = True # p \<longrightarrow>
        (\<exists>r. ((p, r) \<in> (eps A)\<^sup>* \<or> 
             (\<exists>q. (p, q) \<in> (eps A)\<^sup>* \<and> na.fin A q \<and> (na.start A, r) \<in> (eps A)\<^sup>*)) \<and>  s = True # r)"
proof (induct rule : rtrancl_induct) 
   case base show ?case by simp
next
   case step then show ?case by(clarsimp, blast intro: rtrancl_into_rtrancl) 
qed


lemma True_eps_star [iff]:
 "((True # p, s) \<in> (eps (star A))\<^sup>*) =
    (\<exists>r. ((p, r) \<in> (eps A)\<^sup>* \<or> (\<exists>q. (p, q) \<in> (eps A)\<^sup>* \<and> na.fin A q \<and> (na.start A, r) \<in> (eps A)\<^sup>*)) \<and>
         s = True # r)"  (is "?lhs = ?rhs")
proof (rule iffI)
      assume * : "?lhs"
      have  ** : "\<And>p q L R. (p, q) \<in> eps R \<Longrightarrow> (False # p, False # q) \<in> eps (conc L R)"  by simp
      show       "?rhs" 
                by(insert *, drule result, blast )
next
      assume * : "?rhs"
      then show  "?lhs"
                apply (clarify)
                apply (erule disjE)
                apply (erule True_True_eps_starI)
                 apply (clarify)
                apply (rule rtrancl_trans)
                apply (erule True_True_eps_starI)
                apply (rule rtrancl_trans)
                apply (rule r_into_rtrancl)
                apply (erule True_start_eps_starI)
                apply (erule True_True_eps_starI)
                done
qed 


(** True in step Some **)

lemma True_step_star[rule_format,iff] :
 " \<forall>A. ((True # p, r) \<in> step (star A) (Some a)) = (\<exists>q. (p, q) \<in> step A (Some a) \<and> r = True # q)"
unfolding star_def step_def by(simp add: Let_def, blast)


(** True in steps **)

(* reverse list induction! Complicates matters for conc? *)

lemma True_start_steps_starD [rule_format]: 
 "\<forall>rr. (True # na.start A, rr) \<in> steps\<^sub>n\<^sub>a\<^sub>e (star A) w \<longrightarrow>
         (\<exists>us v. w = concat us @ v \<and> (\<forall>u\<in>set us. accepts\<^sub>n\<^sub>a\<^sub>e A u) \<and> 
         (\<exists>r. (na.start A, r) \<in> steps\<^sub>n\<^sub>a\<^sub>e A v \<and> rr = True # r))"

proof (induct w rule:  rev_induct) print_cases
  case Nil  show ?case 
            apply (clarsimp)
            apply (rule_tac x = "[]" in exI)
            apply (auto)
            done
next
  case (snoc x xs) then show ?case
            apply (simp add: O_assoc[symmetric] epsclosure_steps)
            apply (clarify)
            apply (erule allE, erule impE, assumption)
            apply (clarify)
            apply (erule disjE)
             apply (rule_tac x = "us" in exI)
             apply (rule_tac x = "v@[x]" in exI)
             apply (simp add: O_assoc[symmetric] epsclosure_steps)
             apply (blast)
            apply (clarify)
            apply (rule_tac x = "us@[v@[x]]" in exI)
            apply (rule_tac x = "[]" in exI)
            apply (simp add: accepts\<^sub>n\<^sub>a\<^sub>e_def)
            apply (blast)
            done
qed

lemma True_True_steps_starI:
  "\<And>p. (p, q) \<in> steps\<^sub>n\<^sub>a\<^sub>e A w \<Longrightarrow> (True # p, True # q) \<in> steps\<^sub>n\<^sub>a\<^sub>e (star A) w"
apply (induct "w")
 apply (simp)
apply (simp)
apply (blast intro: True_True_eps_starI True_True_step_starI)
done

lemma steps_star_cycle:
 "\<forall>u\<in>set us. accepts\<^sub>n\<^sub>a\<^sub>e A u \<Longrightarrow>
    (True # na.start A, True # na.start A) \<in> steps\<^sub>n\<^sub>a\<^sub>e (star A) (concat us)"
apply (induct "us")
 apply (simp add:accepts\<^sub>n\<^sub>a\<^sub>e_def)
apply (simp add:accepts\<^sub>n\<^sub>a\<^sub>e_def)
apply(blast intro: True_True_steps_starI True_start_eps_starI in_epsclosure_steps)
done

lemma True_start_steps_star:
 "((True # na.start A, rr) \<in> steps\<^sub>n\<^sub>a\<^sub>e (RegExp2NAe.star A) w) =
    (\<exists>us v. w = concat us @ v \<and>
            (\<forall>u\<in>set us. accepts\<^sub>n\<^sub>a\<^sub>e A u) \<and> (\<exists>r. (na.start A, r) \<in> steps\<^sub>n\<^sub>a\<^sub>e A v \<and> rr = True # r)) "
apply (rule iffI)
 apply (erule True_start_steps_starD)
apply (clarify)
apply (blast intro: steps_star_cycle True_True_steps_starI)
done

(** the start state **)

lemma start_step_star[iff]:
  "\<And>A. ((na.start (star A), r) \<in> step (star A) a) =  (a = None \<and> r = True # na.start A)"
by (simp add:star_def step_def Let_def)

lemmas epsclosure_start_step_star =
  in_unfold_rtrancl2[where ?p = "na.start (star A)"] for A

lemma start_steps_star:
 "((na.start (star A), r) \<in> steps\<^sub>n\<^sub>a\<^sub>e (star A) w) =
    (w = [] \<and> r = na.start (star A) \<or> (True # na.start A, r) \<in> steps\<^sub>n\<^sub>a\<^sub>e (star A) w)"
apply (rule iffI)
 apply (case_tac "w")
  apply (simp add: epsclosure_start_step_star)
 apply (simp)
 apply (clarify)
 apply (simp add: epsclosure_start_step_star)
 apply (blast)
apply (erule disjE)
 apply (simp)
apply (blast intro: in_steps_epsclosure)
done

lemma fin_star_True[iff]: "\<And>A. na.fin (star A) (True#p) = na.fin A p"
by (simp add:star_def Let_def)

lemma fin_star_start[iff]: "\<And>A. na.fin (star A) (na.start(star A))"
by (simp add:star_def Let_def)

lemma accepts_star:
 "accepts\<^sub>n\<^sub>a\<^sub>e (star A) w = (\<exists>us. (\<forall>u\<in>set us. accepts\<^sub>n\<^sub>a\<^sub>e A u) \<and> w = concat us)"
apply(unfold accepts\<^sub>n\<^sub>a\<^sub>e_def)
apply (simp add: start_steps_star True_start_steps_star)
apply (rule iffI)
 apply (clarify)
 apply (erule disjE)
  apply (clarify)
  apply (simp)
  apply (rule_tac x = "[]" in exI)
  apply (simp)
 apply (clarify)
 apply (rule_tac x = "us@[v]" in exI)
 apply (simp add: accepts\<^sub>n\<^sub>a\<^sub>e_def)
 apply (blast)
apply (clarify)
apply (rule_tac xs = "us" in rev_exhaust)
 apply (simp)
 apply (blast)
apply (clarify)
apply (simp add: accepts\<^sub>n\<^sub>a\<^sub>e_def)
apply (blast)
done



lemma concat_in_star[rule_format]: "(\<forall>xs\<in>set xss. xs \<in> S) \<longrightarrow> concat xss \<in> RegExp.star S"
by(induct "xss", simp_all add: star.NilI star.ConsI)

lemma in_star: "(w \<in> RegExp.star U) = (\<exists>us. (\<forall>u\<in>set us. u \<in> U) \<and> w = concat us)" (is "?lhs = ?rhs")
proof(rule iffI)
     assume    "?lhs"
     then show "?rhs" 
                proof (induct rule: star.induct)
                      case NilI show ?case              by(rule_tac x ="[]" in exI, simp)
                next
                      case (ConsI a as) then show ?case by(clarify,rule_tac x="a#us" in exI, simp)
                qed
next 
     assume    "?rhs"
     then show "?lhs" by(clarify, simp add: concat_in_star)
qed

section{* Global Approach: Correctness and Completeness *}

lemma sound_and_complete:
 "accepts\<^sub>n\<^sub>a\<^sub>e (rexp2nae rexp) w = (w \<in> L rexp) "
  apply(induct rexp arbitrary : w)
  apply(simp)
       apply (simp add: accepts\<^sub>n\<^sub>a\<^sub>e_def)
     apply (simp add: accepts_atom)
    apply (simp add: accepts_union)
   apply (simp add: accepts_conc)
  apply(simp)
  (*  by (simp add: accepts_star in_star) *)
  sorry

lemmas accepts_rexp2nae = sound_and_complete (* old name *)

end
