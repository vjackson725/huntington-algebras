theory Huntington
  imports Main
begin

(*
  A proof that a Huntington Algebra is a Boolean Algebra, and vice versa

  Following
    http://math.colgate.edu/~amann/MA/robbins_complete.pdf
*)

no_notation disj (infixr "\<or>" 30)
no_notation conj (infixr "\<and>" 35)

(*  Definition of a boolean algebra *)
locale boolean_algebra =
  fixes disj :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" (infixl "\<or>" 70)
    and conj :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" (infixl "\<and>" 70)
    and neg :: "'b \<Rightarrow> 'b"
    and tt :: "'b"
    and ff :: "'b"
  assumes assoc_disj [simp]: "a \<or> (b \<or> c) = a \<or> b \<or> c"
      and comm_disj: "a \<or> b = b \<or> a"
      and assoc_conj [simp]: "a \<and> (b \<and> c) = a \<and> b \<and> c"
      and comm_conj: "a \<and> b = b \<and> a"
      and absorb1 [simp]: "a \<or> (a \<and> b) = a"
      and absorb2 [simp]: "a \<and> (a \<or> b) = a"
      and distrib_disj_over_conj: "a \<or> (b \<and> c) = (a \<or> b) \<and> (a \<or> c)"
      and distrib_conj_over_disj: "a \<and> (b \<or> c) = (a \<and> b) \<or> (a \<and> c)"
      and lem: "a \<or> neg a = tt"
      and noncontra: "a \<and> neg a = ff"
begin

lemma ac_rule_disj: "z \<or> y \<or> x = z \<or> x \<or> y"
  by (metis assoc_disj comm_disj)

lemma ac_rule_conj: "z \<and> y \<and> x = z \<and> x \<and> y"
  by (metis assoc_conj comm_conj)
    
lemma idempotence_disj[simp]: "x \<or> x = x"
proof -
  have "x \<or> x = x \<or> (x \<and> (x \<or> x))"
    by (subst absorb2, rule refl)
  also have "... = x"
    by (subst absorb1[where a="x" and b="x \<or> x"], rule refl)
  finally show ?thesis .
qed

lemma idempotence_conj[simp]: "x \<and> x = x"
  by (metis absorb1 absorb2)

lemma y_disj_absorb_iff_x_conj_absorb: "x \<or> y = y \<longleftrightarrow> x \<and> y = x"
  by (metis absorb1 absorb2 comm_conj comm_disj)
    
lemma neutral_disj_ff[simp]: "x \<or> ff = x"
  using absorb1 noncontra by fastforce

lemma neutral_conj_tt[simp]: "x \<and> tt = x"
  using absorb2 lem by fastforce
    
lemma absorbing_disj_tt[simp]: "x \<or> tt = tt"
  by (metis absorb2 comm_conj comm_disj neutral_conj_tt)

lemma absorbing_conj_ff[simp]: "x \<and> ff = ff"
  by (metis absorb2 comm_conj comm_disj neutral_disj_ff)
    
definition is_complement where
  "is_complement a b \<equiv> HOL.conj (a \<and> b = ff) (a \<or> b = tt)"
    
lemma complement_unique: "\<lbrakk> is_complement x y; is_complement x z \<rbrakk> \<Longrightarrow> y = z"
  unfolding is_complement_def
  by (metis (full_types) distrib_disj_over_conj comm_conj comm_disj idempotence_disj neutral_conj_tt)

lemma complement_neg: "is_complement x (neg x)"
  unfolding is_complement_def
  by (simp add: lem noncontra)
    
lemma double_negation_elim[simp]: "neg (neg x) = x"
  by (metis complement_unique is_complement_def comm_conj comm_disj lem noncontra)
    
lemma neg_injective: "neg x = neg y \<Longrightarrow> x = y"
  by (metis double_negation_elim)

lemma neg_ff_is_tt[simp]: "neg ff = tt"
  by (metis lem noncontra y_disj_absorb_iff_x_conj_absorb)

lemma neg_tt_is_ff[simp]: "neg tt = ff"
  using double_negation_elim neg_ff_is_tt by blast

(* The De Morgan rules *)
lemma demorgan_over_disj[simp]: "neg (x \<or> y) = neg x \<and> neg y"
proof -
  have "(x \<or> y) \<and> (neg x \<and> neg y) = (x \<and> neg x \<and> neg y) \<or> (y \<and> neg x \<and> neg y)"
    by (metis absorbing_conj_ff assoc_conj comm_conj distrib_conj_over_disj noncontra)
  also have "... = (ff \<and> neg y) \<or> (ff \<and> neg x)"
    using ac_rule_conj noncontra by force
  also have "... = ff"
    by (metis absorb1 absorbing_conj_ff comm_conj)
  finally have A: "(x \<or> y) \<and> (neg x \<and> neg y) = ff" .
 
  have "(x \<or> y) \<or> (neg x \<and> neg y) = (x \<or> y \<or> neg x) \<and> (x \<or> y \<or> neg y)"
    by (metis distrib_disj_over_conj)
  also have "... = (y \<or> tt) \<and> (x \<or> tt)"
    by (metis ac_rule_disj assoc_disj lem)
  also have "... = tt"
    by simp
  finally have B: "(x \<or> y) \<or> (neg x \<and> neg y) = tt" .
      
  have "is_complement (x \<or> y) (neg x \<and> neg y)"
    using A B is_complement_def by blast
  thus ?thesis
    using is_complement_def complement_neg complement_unique by blast
qed

lemma demorgan_over_conj[simp]: "neg (x \<and> y) = neg x \<or> neg y"
  by (metis demorgan_over_disj double_negation_elim)

(* The Huntington Equation *)
lemma huntington: "neg (neg x \<or> neg y) \<or> neg (neg x \<or> y) = x"
  by (metis double_negation_elim demorgan_over_disj distrib_conj_over_disj lem neutral_disj_ff)

lemma disj_dual_conj: "a \<or> b = neg (neg a \<and> neg b)"
  by simp

lemma conj_dual_disj: "a \<and> b = neg (neg a \<or> neg b)"
  by simp
    
end

  
(* Definition of a Huntington Algebra *)
locale huntington_algebra =
  fixes disj :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" (infixl "\<or>" 70)
    and neg :: "'b \<Rightarrow> 'b"
  assumes assoc[simp]: "a \<or> (b \<or> c) = a \<or> b \<or> c"
      and comm: "a \<or> b = b \<or> a"
      and huntington[simp]: "neg (neg x \<or> neg y) \<or> neg (neg x \<or> y) = x"
begin

lemma ac_rule: "z \<or> y \<or> x = z \<or> x \<or> y"
  by (metis assoc comm)
    
lemma xnx_eq_nxnnx[simp]: "neg x \<or> neg (neg x) = x \<or> neg x"
proof -
  have "neg x \<or> neg (neg x) = neg (neg (neg (neg x)) \<or> neg x) \<or> neg (neg (neg (neg x)) \<or> neg (neg x)) \<or> neg (neg (neg x) \<or> neg x) \<or> neg (neg (neg x) \<or> neg (neg x))"
    by (metis huntington[where y="neg x"] assoc comm)
  also have "... = neg (neg x \<or> neg (neg (neg x))) \<or> neg (neg x \<or> neg (neg x)) \<or> neg (neg (neg x) \<or> neg (neg (neg x))) \<or> neg (neg (neg x) \<or> neg (neg x))"
    proof (rule arg_cong[where f="\<lambda>z. z \<or> neg (neg (neg x) \<or> neg (neg x))"])
      show "neg (neg (neg (neg x)) \<or> neg x) \<or> neg (neg (neg (neg x)) \<or> neg (neg x)) \<or> neg (neg (neg x) \<or> neg x) =
           neg (neg x \<or> neg (neg (neg x))) \<or> neg (neg x \<or> neg (neg x)) \<or> neg (neg (neg x) \<or> neg (neg (neg x)))"
        by (metis ac_rule comm)
    qed
  also have "... = x \<or> neg x"
    by (metis huntington[where y="neg (neg x)"] assoc comm)
  finally show ?thesis .
qed

lemma double_negation_elim[simp]: "neg (neg x) = x"
proof -
  have "neg (neg x) = neg (neg (neg (neg x)) \<or> neg (neg x)) \<or> neg (neg (neg (neg x)) \<or> neg x)"
    by (simp only: huntington[symmetric, where y="neg x"])
  also have "... = neg (neg x \<or> neg (neg (neg x))) \<or> neg (neg x \<or> neg (neg x))"
    by (simp only: xnx_eq_nxnnx comm)
  also have "... = x"
    by (simp only: huntington[where y="neg (neg x)"])
  finally show ?thesis .
qed

lemma neg_injective: "neg x = neg y \<Longrightarrow> x = y"
  by (metis double_negation_elim)

(* Define conj as the dual operation of disj *)
definition conj (infixl "\<and>" 70) where
  "a \<and> b = neg (neg a \<or> neg b)"
  
lemma assoc_conj[simp]: "a \<and> (b \<and> c) = a \<and> b \<and> c"
  unfolding conj_def
  by simp

lemma comm_conj: "a \<and> b = b \<and> a"
  unfolding conj_def
  by (simp add: comm)

lemma ac_rule_conj: "z \<and> y \<and> x = z \<and> x \<and> y"
  by (metis assoc_conj comm_conj)

lemma demorgan_over_disj: "neg (x \<or> y) = neg x \<and> neg y"
  unfolding conj_def
  by simp

lemma demorgan_over_conj[simp]: "neg (x \<and> y) = neg x \<or> neg y"
  unfolding conj_def
  using double_negation_elim by blast

lemma huntington2[simp]: "(x \<and> y) \<or> (x \<and> neg y) = x"
  unfolding conj_def
  using huntington by force

lemma tt_unique: "x \<or> neg x = y \<or> neg y"
proof -
  have "x \<or> neg x = (x \<and> neg y) \<or> (x \<and> neg (neg y)) \<or> (neg x \<and> neg y) \<or> (neg x \<and> neg (neg y))"
    by (metis assoc huntington2[where y="neg y"])
  also have "... = (neg y \<and> x) \<or> (neg y \<and> neg x) \<or> (y \<and> x) \<or> (y \<and> neg x)"
    by (simp only: double_negation_elim comm_conj assoc ac_rule)
  also have "... = y \<or> neg y"
    by (metis assoc comm huntington2)
  finally show ?thesis .
qed

lemma ff_unique: "x \<and> neg x = y \<and> neg y"
  unfolding conj_def
  by (metis tt_unique)

(* define tt as excluded middle *)    
definition tt where
  "tt \<equiv> (THE y. \<forall>x. x \<or> neg x = y)"

definition ff where
  "ff \<equiv> neg tt"

(* show non-contradiction is false *)  
lemma noncontra[simp]: "x \<and> neg x = ff"
proof -
  have "\<exists>!y. (\<forall>x. x \<or> neg x = y)"
    by (metis tt_unique)
  hence "\<forall>x. x \<or> neg x = (THE x. \<forall>xa. xa \<or> neg xa = x)"
    by (rule theI')
  hence "neg x \<or> x = (THE y. \<forall>x. x \<or> neg x = y)"
    by (metis comm)
  thus "x \<and> neg x = ff"
    unfolding ff_def tt_def
    by (simp add: conj_def)
qed
  
(* Show law of excluded middle *)
lemma lem[simp]: "x \<or> neg x = tt"
  by (metis demorgan_over_disj ff_def neg_injective noncontra)

lemma tt_dup[simp]: "tt \<or> tt = tt"
  by (metis assoc huntington demorgan_over_conj double_negation_elim noncontra xnx_eq_nxnnx)
  
lemma ff_dup[simp]: "ff \<or> ff = ff"
proof -
  have "ff \<or> ff = neg (tt \<or> tt) \<or> neg tt"
    using ff_def tt_dup by simp
  also have "... = neg tt"
    by (metis ff_def huntington2 demorgan_over_disj noncontra)
  also have "... = ff"
    by (simp only: ff_def)
  finally show "ff \<or> ff = ff" .
qed
    
lemma neutral_disj_ff[simp]: "x \<or> ff = x"
  by (metis assoc ff_dup huntington2 noncontra)

lemma neutral_conj_tt[simp]: "x \<and> tt = x"
  using ff_def neg_injective neutral_disj_ff by simp

lemma idempotence_disj[simp]: "x \<or> x = x"
  by (metis demorgan_over_disj huntington2 neg_injective neutral_disj_ff noncontra)

lemma idempotence_conj[simp]: "x \<and> x = x"
  by (metis huntington2 neutral_disj_ff noncontra)

lemma absorbing_disj_tt[simp]: "x \<or> tt = tt"
  by (metis assoc idempotence_disj lem)

lemma absorbing_conj_ff[simp]: "x \<and> ff = ff"
  by (metis ac_rule_conj comm_conj idempotence_conj noncontra)
    
lemma absorb1 [simp]: "a \<or> (a \<and> b) = a"
  by (metis comm huntington2 assoc idempotence_disj)
  
lemma absorb2 [simp]: "a \<and> (a \<or> b) = a"
  by (simp add: demorgan_over_disj neg_injective)

(* Show the distributive laws *)
lemma distrib_conj_over_disj: "x \<and> (y \<or> z) = (x \<and> y) \<or> (x \<and> z)"
proof -
  have "x \<and> (y \<or> z) = (x \<and> (y \<or> z) \<and> y) \<or> (x \<and> (y \<or> z) \<and> neg y)"
    by simp      
  also have "... = (x \<and> y) \<or> (x \<and> (y \<or> z) \<and> neg y)"
    by (metis absorb2 ac_rule_conj comm_conj)
  also have "... = (x \<and> y \<and> z) \<or> (x \<and> y \<and> neg z) \<or> (x \<and> neg y \<and> z \<and> (y \<or> z)) \<or> (x \<and> (y \<or> z) \<and> neg y \<and> neg z)"
      by (metis ac_rule_conj assoc huntington2)
  also have "... = (x \<and> y \<and> z) \<or> (x \<and> y \<and> neg z) \<or> (x \<and> neg y \<and> z) \<or> (x \<and> (y \<or> z) \<and> neg (y \<or> z))"
    proof -
      have "x \<and> neg y \<and> z = x \<and> neg y \<and> z \<and> (y \<or> z)"
        by (metis absorb2 assoc_conj comm)
      then show ?thesis
        using demorgan_over_disj by force
    qed
  also have "... = (x \<and> y \<and> z) \<or> (x \<and> y \<and> neg z) \<or> (x \<and> neg y \<and> z)"
    by (metis absorbing_conj_ff assoc_conj neutral_disj_ff noncontra)
  also have "... = (x \<and> y \<and> z) \<or> (x \<and> y \<and> neg z) \<or> (((x \<and> z) \<and> y) \<or> ((x \<and> z) \<and> neg y))"
    by (simp add: ac_rule_conj)
  also have "... = (x \<and> y) \<or> (x \<and> z)"
    by (simp only: huntington2)
  finally show ?thesis .
qed

lemma distrib_disj_over_conj: "a \<or> (b \<and> c) = (a \<or> b) \<and> (a \<or> c)"
  by (metis conj_def demorgan_over_disj distrib_conj_over_disj double_negation_elim)
end

(* 
  The main theorems

  Given a boolean algebra, we have a huntington algebra
*)
theorem B_imp_H: "boolean_algebra disj' conj' neg' tt ff \<Longrightarrow> huntington_algebra disj' neg'"
proof -
  assume B: "boolean_algebra disj' conj' neg' tt ff"
  show ?thesis
  proof unfold_locales
    show "\<And>a b c. disj' a (disj' b c) = disj' (disj' a b) c"
      using B boolean_algebra.assoc_disj by metis
  next
    show "\<And>a b. disj' a b = disj' b a"
      using B boolean_algebra.comm_disj by metis
  next
    show "\<And>x y. disj' (neg' (disj' (neg' x) (neg' y))) (neg' (disj' (neg' x) y)) = x"
      using B boolean_algebra.huntington by metis
  qed
qed

(* 
  The main theorems

  Given a huntington algebra, we can construct a boolean algebra
*)
theorem H_imp_B: "\<lbrakk> huntington_algebra disj' neg'; conj' = huntington_algebra.conj disj' neg';
                    tt = huntington_algebra.tt disj' neg'; ff = huntington_algebra.ff disj' neg' \<rbrakk> \<Longrightarrow>
                  boolean_algebra disj' conj' neg' tt ff"
proof -
  assume H: "huntington_algebra disj' neg'"
     and A: "conj' = huntington_algebra.conj disj' neg'"
     and T: "tt = huntington_algebra.tt disj' neg'"
     and F: "ff = huntington_algebra.ff disj' neg'"

  show ?thesis
  proof unfold_locales
    show "\<And>a b c. disj' a (disj' b c) = disj' (disj' a b) c"
      by (meson H huntington_algebra.assoc)
  next
    show "\<And>a b. disj' a b = disj' b a"
      by (meson H huntington_algebra.comm)
  next  
    show "\<And>a b c. conj' a (conj' b c) = conj' (conj' a b) c"
      by (simp only: H A huntington_algebra.assoc_conj)
  next
    show "\<And>a b. conj' a b = conj' b a"
      by (simp only: A H huntington_algebra.comm_conj)
  next
    show  "\<And>a b. disj' a (conj' a b) = a"
      by (simp only: H A huntington_algebra.absorb1)
  next
    show  "\<And>a b. conj' a (disj' a b) = a"
      by (simp only: H A huntington_algebra.absorb2)
  next
    show "\<And>a b c. disj' a (conj' b c) = conj' (disj' a b) (disj' a c)"
      by (simp only: H A huntington_algebra.distrib_disj_over_conj)
  next
    show  "\<And>a b c. conj' a (disj' b c) = disj' (conj' a b) (conj' a c)"
      by (simp only: H A huntington_algebra.distrib_conj_over_disj)
  next
    show "\<And>a. disj' a (neg' a) = tt"
      by (simp only: H T huntington_algebra.lem)
  next
    show "\<And>a. conj' a (neg' a) = ff"
      by (simp only: H A F huntington_algebra.noncontra)
  qed
qed

end