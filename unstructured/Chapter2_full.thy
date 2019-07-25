theory Chapter2_prob
  imports Main HOL.Zorn HOL.Order_Relation "HOL.Real"
  "HOL-Library.Lattice_Syntax" "HOL-Library.Finite_Lattice"
  HOL.Finite_Set
begin
section \<open>Preliminary Matters\<close>
datatype bool2 = t2 | f2

fun leq2 :: \<open>bool2 \<Rightarrow> bool2 \<Rightarrow> bool\<close> where
\<open>leq2 t2 t2 = True\<close> |
\<open>leq2 f2 f2 = True\<close> |
\<open>leq2 _ _ = False\<close>

lemma leq2_refl: "leq2 b b = True" by(cases b) auto
lemma leq2_antisym: " \<lbrakk> leq2 u v ; leq2 v u \<rbrakk> \<Longrightarrow> u = v" by(cases u; cases v) auto
lemma leq2_trans: " \<lbrakk> leq2 u v; leq2 v w \<rbrakk> \<Longrightarrow> leq2 u w" by(cases u; cases v; cases w) auto

instantiation bool2 :: order
begin

definition less_eq_bool2_def: \<open> b1 \<le> b2 = leq2 b1 b2 \<close>
definition less_bool2_def: \<open> b1 < b2 = ((leq2 b1 b2) \<and> (b1 \<noteq> b2))\<close>

instance proof
  fix x y :: bool2
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" unfolding less_eq_bool2_def less_bool2_def by(cases x; cases y) auto
next
  fix x :: bool2
  from leq2_refl show " x \<le> x" unfolding less_eq_bool2_def by auto
next
  fix x y z :: bool2
  from leq2_trans show " x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" unfolding less_eq_bool2_def by auto
next
  fix x y :: bool2
  from leq2_antisym show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" unfolding less_eq_bool2_def by auto
qed
end

datatype bool3 = n3 | t3 | f3

fun leq3 :: \<open>bool3 \<Rightarrow> bool3 \<Rightarrow> bool\<close> where
\<open>leq3 n3 n3 = True\<close> |
\<open>leq3 t3 t3 = True\<close> |
\<open>leq3 f3 f3 = True\<close> |
\<open>leq3 n3 t3 = True\<close> |
\<open>leq3 n3 f3 = True\<close> |
\<open>leq3 t3 n3 = False\<close> |
\<open>leq3 t3 f3 = False\<close> |
\<open>leq3 f3 n3 = False\<close> |
\<open>leq3 f3 t3 = False\<close>

lemma leq3_refl: "leq3 (b :: bool3) b = True" by(cases b) auto
lemma leq3_antisym: " \<lbrakk> leq3 u v ; leq3 v u \<rbrakk> \<Longrightarrow> u = v" by(cases u; cases v) auto
lemma leq3_trans: " \<lbrakk> leq3 u v; leq3 v w \<rbrakk> \<Longrightarrow> leq3 u w" by(cases u; cases v; cases w) auto

instantiation bool3 :: order
begin

definition less_eq_bool3_def: \<open> b1 \<le> b2 = leq3 b1 (b2 :: bool3) \<close>
definition less_bool3_def: \<open> b1 < b2 = ((leq3 b1 (b2 :: bool3)) \<and> (b1 \<noteq> b2))\<close>

instance proof
  fix x y :: bool3
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" unfolding less_eq_bool3_def less_bool3_def by(cases x; cases y) auto
next
  fix x :: bool3
  from leq3_refl show " x \<le> x" unfolding less_eq_bool3_def by auto
next
  fix x y z :: bool3
  from leq3_trans show " x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" unfolding less_eq_bool3_def by auto
next
  fix x y :: bool3
  from leq3_antisym show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" unfolding less_eq_bool3_def by auto
qed
end

datatype bool4 = n4 | t4 | f4 | b4

fun leq4 :: \<open>bool4 \<Rightarrow> bool4 \<Rightarrow> bool\<close> where
\<open>leq4 _ b4 = True\<close> |
\<open>leq4 n4 _ = True\<close> |
\<open>leq4 t4 n4 = False\<close> |
\<open>leq4 t4 t4 = True \<close> |
\<open>leq4 t4 f4 = False\<close> |
\<open>leq4 f4 n4 = False\<close> |
\<open>leq4 f4 t4 = False\<close> |
\<open>leq4 f4 f4 = True\<close> |
\<open>leq4 b4 n4 = False\<close> |
\<open>leq4 b4 t4 = False\<close> |
\<open>leq4 b4 f4 = False\<close>

lemma leq4_refl: "leq4 b b = True" by(cases b) auto
lemma leq4_antisym: " \<lbrakk> leq4 u v ; leq4 v u \<rbrakk> \<Longrightarrow> u = v" by(cases u; cases v) auto
lemma leq4_trans: " \<lbrakk> leq4 u v; leq4 v w \<rbrakk> \<Longrightarrow> leq4 u w" by(cases u; cases v; cases w) auto

instantiation bool4 :: order
begin

definition less_eq_bool4_def: \<open> b1 \<le> b2 = leq4 b1 (b2 :: bool4) \<close>
definition less_bool4_def: \<open> b1 < b2 = ((leq4 b1 (b2 :: bool4)) \<and> (b1 \<noteq> b2))\<close>

instance proof
  fix x y :: bool4
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" unfolding less_eq_bool4_def less_bool4_def by(cases x; cases y) auto
next
  fix x :: bool4
  from leq4_refl show " x \<le> x" unfolding less_eq_bool4_def by auto
next
  fix x y z :: bool4
  from leq4_trans show " x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" unfolding less_eq_bool4_def by auto
next
  fix x y :: bool4
  from leq4_antisym show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" unfolding less_eq_bool4_def by auto
qed
end

fun inf4 :: \<open>bool4 \<Rightarrow> bool4 \<Rightarrow> bool4\<close> where
"inf4 n4 (b :: bool4) = n4" |
"inf4 (b :: bool4) b4 = b" |
"inf4 (b :: bool4) n4 = n4" |
"inf4 b4 (b :: bool4) = b" |
"inf4 t4 t4 = t4" | "inf4 f4 f4 = f4" |
"inf4 t4 f4 = n4" | "inf4 f4 t4 = n4" 

fun sup4 :: \<open>bool4 \<Rightarrow> bool4 \<Rightarrow> bool4\<close> where
"sup4 n4 (b :: bool4) = b" |
"sup4 (b :: bool4) b4 = b4" |
"sup4 (b :: bool4) n4 = b" |
"sup4 b4 (b :: bool4) = b4" |
"sup4 t4 t4 = t4" | "sup4 f4 f4 = f4" |
"sup4 t4 f4 = b4" | "sup4 f4 t4 = b4"

instantiation bool4 :: semilattice_inf
begin

definition inf_bool4_def: "inf b1 (b2 :: bool4) = inf4 b1 b2" 

instance proof
  fix x y :: bool4
  show "inf x y \<le> x" unfolding inf_bool4_def less_eq_bool4_def by(cases x; cases y) auto
next
fix x y :: bool4
  show "inf x y \<le> y" unfolding inf_bool4_def less_eq_bool4_def by(cases x; cases y) auto
next
  fix x y z :: bool4
  show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> inf y z" unfolding inf_bool4_def less_eq_bool4_def by(cases x; cases y; cases z) auto
qed
end

instantiation bool4 :: semilattice_sup
begin

definition sup_bool4_def: "sup b1 (b2 :: bool4) = sup4 b1 b2" 

instance proof
  fix x y :: bool4
  show " x \<le> sup x y" unfolding sup_bool4_def less_eq_bool4_def by(cases x; cases y) auto
next
fix x y :: bool4
  show " y \<le> sup x y" unfolding sup_bool4_def less_eq_bool4_def by(cases x; cases y) auto
next
  fix y x z :: bool4
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> sup y z \<le> x" unfolding sup_bool4_def less_eq_bool4_def by(cases x; cases y; cases z) auto
qed
end

instantiation bool4 :: lattice
begin
instance proof qed
end

lemma bool4_induct: "P n4 \<Longrightarrow> P t4 \<Longrightarrow> P f4 \<Longrightarrow> P b4 \<Longrightarrow> P x" by(cases x) auto

lemma UNIV_bool4: "UNIV = {n4, t4, f4, b4}"
  proof(auto intro: bool4_induct)
    show "\<And>x. x \<noteq> n4 \<Longrightarrow> x \<noteq> t4 \<Longrightarrow> x \<noteq> f4 \<Longrightarrow> x = b4" proof -
      fix x::bool4
      show "x \<noteq> n4 \<Longrightarrow> x \<noteq> t4 \<Longrightarrow> x \<noteq> f4 \<Longrightarrow> x = b4" by(cases x) auto
    qed
  qed

instantiation bool4 :: finite
begin
instance by standard(simp add: UNIV_bool4)
end

instantiation bool4 :: finite_lattice_complete
begin

definition Inf_bool4_def: "Inf (X :: bool4 set) = Finite_Set.fold inf b4 X "
definition Sup_bool4_def: "Sup (X :: bool4 set) = Finite_Set.fold sup n4 X "

definition bot_bool4_def: "bot = n4"
definition top_bool4_def: "top = b4"

instance proof 
  show "(bot :: bool4) = Inf_fin UNIV"
    by (simp add: UNIV_bool4 bot_bool4_def inf_bool4_def)
next
  show "(top :: bool4) = Sup_fin UNIV"
    by (simp add: UNIV_bool4 sup_bool4_def top_bool4_def)
next
  fix A :: "bool4 set"
  show "\<Sqinter>A = Finite_Set.fold (\<sqinter>) \<top> A"
    by (simp add: Inf_bool4_def top_bool4_def)
next
  fix A :: "bool4 set"
  show " \<Squnion>A = Finite_Set.fold (\<squnion>) \<bottom> A" 
    by (simp add: Sup_bool4_def bot_bool4_def)
qed
end

lemma \<open> \<Squnion> {n4,t4,f4} = b4\<close> 
  by (metis Sup_UNIV Sup_insert UNIV_bool4 ccpo_Sup_singleton sup4.simps(12) sup4.simps(2) sup4.simps(3) sup_bool4_def top_bool4_def)

abbreviation upper_bound :: "'a::order \<Rightarrow> 'a set \<Rightarrow> bool" (infix "\<greatersim>" 60) where
"upper_bound x Y \<equiv> \<forall> y \<in> Y. x \<ge> y"

abbreviation lower_bound :: "'a::order \<Rightarrow> 'a set \<Rightarrow> bool" (infix "\<lesssim>" 60)where
"lower_bound x Y \<equiv> \<forall> y \<in> Y. x \<le> y"

definition supR :: "'a ::order \<Rightarrow> 'a set \<Rightarrow> bool" where
"supR (x::'a) (Y::'a set) \<equiv> ( x \<greatersim> Y ) \<and> (\<forall> y. y \<greatersim> Y  \<longrightarrow> x \<le> y)"

definition supRs :: "'a ::order \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
"supRs (x::'a) (Y::'a set) (X :: 'a set)  \<equiv> (x \<in> X) \<and> ( x \<greatersim> Y ) \<and> (\<forall> y \<in> X. y \<greatersim> Y  \<longrightarrow> x \<le> y)"

definition infR :: "'a ::order \<Rightarrow> 'a set \<Rightarrow> bool" where
"infR (x::'a) (Y :: 'a set) \<equiv> ( x \<lesssim> Y) \<and> (\<forall> y. y \<lesssim> Y \<longrightarrow> x \<ge> y)"

definition infRs :: "'a ::order \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
"infRs (x::'a) (Y :: 'a set) (X :: 'a set) \<equiv> (x \<in> X) \<and> ( x \<lesssim> Y) \<and> (\<forall> y \<in> X. y \<lesssim> Y \<longrightarrow> x \<ge> y)"

definition lattice :: "('a ::order) set  \<Rightarrow> bool" where
"lattice X \<equiv> (\<forall> X' \<subseteq> X. X' \<noteq> {} \<and> finite X' \<longrightarrow> (\<exists> s. supR s X') \<and> (\<exists> i. infR i X') )"

definition complete_latticeR :: "('a ::order) set \<Rightarrow> bool" where
"complete_latticeR X \<equiv> (\<forall> X' \<subseteq> X. (\<exists> s \<in> X. supRs s X' X) \<and> (\<exists> i \<in> X. infRs i X' X) )"

lemma supRs_prop: "supRs x Y X \<Longrightarrow> x \<in> X" by(simp add: supRs_def)

lemma complete_lattice_iff_sup:
"complete_latticeR X \<longleftrightarrow> (\<forall> X' \<subseteq> X. (\<exists> s \<in> X. supRs s X' X))"
proof
  assume "complete_latticeR X"
  from this show "\<forall>X'\<subseteq>X. \<exists>s\<in>X. supRs s X' X" by(simp add: complete_latticeR_def)
next
  assume Hsup: "\<forall>X'\<subseteq>X. \<exists>s\<in>X. supRs s X' X"
  have "(\<forall> X' \<subseteq> X. (\<exists> s \<in> X. supRs s X' X) \<and> (\<exists> i \<in> X. infRs i X' X) )" proof
    fix X'
    show "X' \<subseteq> X \<longrightarrow> (\<exists> s \<in> X. supRs s X' X) \<and> (\<exists> i \<in> X. infRs i X' X)" proof
      assume HX':"X' \<subseteq> X"
      show "(\<exists> s \<in> X. supRs s X' X) \<and> (\<exists> i \<in> X. infRs i X' X)" proof
        from HX' Hsup show "(\<exists> s \<in> X. supRs s X' X)" by auto
      next
        have "{y \<in> X. y \<lesssim> X'} \<subseteq> X" by auto
        from this Hsup have "\<exists> s \<in> X. supRs s {y \<in> X. y \<lesssim> X'} X" by simp
        then obtain s where s1: "s \<in> X" and s2: "supRs s {y \<in> X. y \<lesssim> X'} X" by auto
        from s2 supRs_def[of "s" "{y \<in> X. y \<lesssim> X'}" "X"] have s3: "s \<lesssim> X'"
          using HX' by blast
        from s2 supRs_def[of "s" "{y \<in> X. y \<lesssim> X'}" "X"] have s4: "\<forall> y \<in> X. y \<lesssim> X' \<longrightarrow> y \<le> s"
          by simp
        show " \<exists>i\<in>X. infRs i X' X" proof
          from s1 s3 s4 show "infRs s X' X" by(simp add: infRs_def)
        next
          from s1 show "s \<in> X" by auto
        qed
      qed
    qed
  qed
  from this show "complete_latticeR X" by (simp add: complete_latticeR_def)
qed

lemma complete_lattice_iff_inf:
"complete_latticeR X \<longleftrightarrow> (\<forall> X' \<subseteq> X. (\<exists> s \<in> X. infRs s X' X))"
proof
  assume "complete_latticeR X"
  from this show "\<forall>X'\<subseteq>X. \<exists>s\<in>X. infRs s X' X" by(simp add: complete_latticeR_def)
next
  assume Hinf: "\<forall>X'\<subseteq>X. \<exists>s\<in>X. infRs s X' X"
  have "(\<forall> X' \<subseteq> X. (\<exists> s \<in> X. supRs s X' X) \<and> (\<exists> i \<in> X. infRs i X' X) )" proof
    fix X'
    show "X' \<subseteq> X \<longrightarrow> (\<exists> s \<in> X. supRs s X' X) \<and> (\<exists> i \<in> X. infRs i X' X)" proof
      assume HX':"X' \<subseteq> X"
      show "(\<exists> s \<in> X. supRs s X' X) \<and> (\<exists> i \<in> X. infRs i X' X)" proof
        from HX' Hinf show "(\<exists> s \<in> X. infRs s X' X)" by auto
      next
        have "{y \<in> X. y \<greatersim> X'} \<subseteq> X" by auto
        from this Hinf have "\<exists> s \<in> X. infRs s {y \<in> X. y \<greatersim> X'} X" by simp
        then obtain s where s1: "s \<in> X" and s2: "infRs s {y \<in> X. y \<greatersim> X'} X" by auto
        from s2 infRs_def[of "s" " {y \<in> X. y \<greatersim> X'}" "X"] have s3: "s \<greatersim> X'"
          using HX' by blast
        from s2 infRs_def[of "s" " {y \<in> X. y \<greatersim> X'}" "X"] have s4: "\<forall> y \<in> X. y \<greatersim> X' \<longrightarrow> y \<ge> s" 
          by simp
        show " \<exists>i\<in>X. supRs i X' X" proof
          from s1 s3 s4 show "supRs s X' X" by(simp add: supRs_def)
        next
          from s1 show "s \<in> X" by auto
        qed
      qed
    qed
  qed
  from this show "complete_latticeR X" by (simp add: complete_latticeR_def)
qed

lemma order_example1:" supRs t3 {t3, n3} {t3, n3, f3}"
  by(simp add: supRs_def less_eq_bool3_def)

lemma order_example1B:" supRs f3 {f3, n3} {t3, n3, f3}"
  by(simp add: supRs_def less_eq_bool3_def)

lemma order_example2:" infR n3 {t3, n3}"
  by (simp add: infR_def less_eq_bool3_def)

lemma order_example3: " infR n3 {t3, f3}"
  by (smt bool3.exhaust infR_def insertI1 insert_subset leq3.simps(1) leq3.simps(4) leq3.simps(5) leq3.simps(7) leq3.simps(9) less_eq_bool3_def subset_insertI)

lemma order_example4: "\<not> supR b {t3, f3}"
  by(cases b; simp add: supR_def less_eq_bool3_def)

lemma order_example5: "\<not> upper_bound b {t3, f3}"
  by(cases b; simp add: less_eq_bool3_def)

context order
begin
definition consi :: \<open>'a  set \<Rightarrow> 'a set \<Rightarrow> bool\<close> where
\<open>consi Y X \<longleftrightarrow> ( \<forall> x \<in> Y. \<forall> y \<in> Y. \<exists> b \<in> X. (x \<le> b \<and> y \<le> b) )\<close>
end

lemma consi_subset: "\<lbrakk> X' \<subseteq> X; consi Y X'\<rbrakk> \<Longrightarrow> consi Y X"
  by (smt consi_def subset_eq)

class Vccpo = order + Sup +
  assumes Vccpo_Sup_upper : \<open>consi A UNIV \<Longrightarrow> x \<in> A \<Longrightarrow> x \<le> Sup A\<close>
  assumes Vccpo_Sup_least: \<open>consi A UNIV \<Longrightarrow> (\<And> x. x \<in> A \<Longrightarrow> x \<le> z) \<Longrightarrow> Sup A \<le> z\<close>

fun sup3 :: \<open>bool3 \<Rightarrow> bool3 \<Rightarrow> bool3\<close> where
"sup3 n3 (b :: bool3) = b" |
"sup3 (b :: bool3) n3 = b" |
"sup3 t3 t3 = t3" | "sup3 f3 f3 = f3" |
"sup3 t3 f3 = undefined" | "sup3 f3 t3 = undefined"

(*
fun sup3_lift :: \<open>bool3 \<Rightarrow> bool3 \<Rightarrow> bool3\<close> where
"sup3_lift (Some b1) (Some b2) = sup3 b1 b2" |
"sup3_lift _ None = None" | "sup3_lift None _ = None"
*)

lemma bool3_induct: "P n3 \<Longrightarrow> P t3 \<Longrightarrow> P f3 \<Longrightarrow> P x" by(cases x) auto

lemma UNIV_bool3: "UNIV = {n3, t3, f3}"
  proof(auto intro: bool3_induct)
    show "\<And>x. x \<noteq> n3 \<Longrightarrow> x \<noteq> t3 \<Longrightarrow> x = f3" proof -
      fix x::bool3
      show "x \<noteq> n3 \<Longrightarrow> x \<noteq> t3 \<Longrightarrow> x = f3" by(cases x) auto
    qed
  qed

instantiation bool3 :: finite
begin
instance by standard(simp add: UNIV_bool3)
end

lemma bool3_set_cases:
"((X::bool3 set) = {} \<or> X = {t3} \<or> X = {f3} \<or> X = {n3} \<or> X = {t3, f3} \<or> X = {t3, n3} \<or> X = {f3, n3} \<or> X = {t3, f3, n3})"
proof -
  fix X :: \<open>bool3 set\<close>
  have I1: "finite X" by auto
  have I2: "{} = {} \<or> {} = {t3} \<or> {} = {f3} \<or> {} = {n3} \<or>{} = {t3, f3} \<or> {} = {t3, n3} \<or> {} = {f3, n3} \<or> {} = {t3, f3, n3}" by auto
  have I3: "(\<And>x F. finite F \<Longrightarrow> x \<notin> F \<Longrightarrow> F = {} \<or> F = {t3} \<or> F = {f3} \<or>
            F = {n3} \<or> F = {t3, f3} \<or> F = {t3, n3} \<or> F = {f3, n3} \<or>
            F = {t3, f3, n3} \<Longrightarrow> (insert x F = {} \<or> insert x F = {t3} \<or>
            insert x F = {f3} \<or> insert x F = {n3} \<or> insert x F = {t3, f3} \<or>
            insert x F = {t3, n3} \<or> insert x F = {f3, n3} \<or> insert x F =
            {t3, f3, n3}))" proof -
    fix x :: bool3
    fix F :: "bool3 set"
    assume A1: "finite F"
    assume A2: "x \<notin> F"
    assume A3: "F = {} \<or> F = {t3} \<or> F = {f3} \<or>
            F = {n3} \<or> F = {t3, f3} \<or> F = {t3, n3} \<or> F = {f3, n3} \<or>
            F = {t3, f3, n3}"
    show "(insert x F = {} \<or> insert x F = {t3} \<or>
            insert x F = {f3} \<or> insert x F = {n3} \<or> insert x F = {t3, f3} \<or>
            insert x F = {t3, n3} \<or> insert x F = {f3, n3} \<or> insert x F =
            {t3, f3, n3})"
      by (smt A2 A3 bool3.exhaust insertI1 insert_commute)
  qed
  from I1 I2 I3 finite_induct[of X "(\<lambda> x. x={} \<or> x = {t3} \<or> x = {f3} \<or> x = {n3} \<or> x = {t3, f3} \<or> x = {t3, n3} \<or> x = {f3, n3} \<or> x = {t3, f3, n3})"]
  show " X = {} \<or> X = {t3} \<or> X = {f3} \<or> X = {n3} \<or> X = {t3, f3} \<or> X = {t3, n3} \<or>
        X = {f3, n3} \<or> X = {t3, f3, n3}" by auto
qed

instantiation bool3 :: Sup
begin
definition Sup_bool3_def:
"Sup (X :: bool3 set) = Finite_Set.fold sup3 n3 X"
instance proof qed
end

(*
lemma order_example1fun: "Sup {t3, n3} = t3"
proof-
  have "Finite_Set.fold sup3 n3 {t3, n3} = t3" try
  thus ?thesis by(simp add: Sup_bool3_def)
qed

lemma order_example1Bfun:" supRs f3 {f3, n3} {t3, n3, f3}"
  by(simp add: supRs_def less_eq_bool3_def)

instantiation bool3 :: Vccpo
instance proof
  fix A :: \<open>bool3 set\<close>
  assume H: "consi A UNIV"
  fix x :: bool3
  from bool3_set_cases have \<open>A = {} \<or> A = {t3} \<or> A = {f3} \<or> A = {n3} \<or> A = {t3, f3} \<or> A = {t3, n3} \<or> A = {f3, n3} \<or> A = {t3, f3, n3}\<close> by auto
  from this Sup_bool3_def show "x \<in> A \<Longrightarrow> x \<le> Sup A" try by(cases x) auto
    
    by(cases x)
 *)
section \<open>Coherent Complete Partial Orders\<close>

definition ccpo ::\<open>('a ::order) set \<Rightarrow> bool\<close> where
"ccpo X \<equiv> ( \<forall> X' \<subseteq> X. (consi X' X) \<longrightarrow> (\<exists> b \<in> X. supRs b X' X) )"

lemma empty_consi: "consi {} X" by(simp add: consi_def)

lemma C1: "consi { b :: bool3} {n3, t3, f3}"
  using bool3.exhaust consi_def by blast

lemma C2: "consi {n3, t3} {n3, t3, f3}"
  by (metis consi_def doubleton_eq_iff insert_subset order_example1 subset_insertI supRs_def)

lemma C3: "consi {n3, f3} {n3, t3, f3}"
  by (metis consi_def doubleton_eq_iff insert_subset order_example1B subset_insertI supRs_def)

lemma C4_helper: "\<not> ( \<exists> b::bool3. b \<greatersim> {t3, f3})"
  using order_example5 by blast

lemma C4: "\<not> consi {t3, f3} {n3, t3, f3}" proof
  assume "consi {t3, f3} {n3, t3, f3}"
  from this have "\<exists> b \<in> {n3,t3, f3}. b \<ge> t3 \<and> b \<ge> f3"
    by (simp add: consi_def)
  from this C4_helper show "False" by auto
  qed

lemma C5: "\<not> consi {t3, f3, n3} {n3, t3,f3}" 
  using C4 by (simp add: consi_def; blast)

lemma "\<not> ccpo {}" by(simp add: ccpo_def consi_def)

lemma complete_lattice_implies_ccpo:
"complete_latticeR (X :: ('a :: order) set) \<Longrightarrow> ccpo X"
  by (simp add: ccpo_def complete_lattice_iff_sup)

lemma ccpo_least_element:
"ccpo (X :: ('a ::order) set) \<Longrightarrow> \<exists>l\<in>X. l \<lesssim> X"
  by (metis ccpo_def empty_iff empty_subsetI supRs_def consi_def)

lemma ccpo_nonempty_has_inf:
"\<lbrakk> ccpo (X :: ('a ::order) set) ; X' \<subseteq> X; X' \<noteq> {} \<rbrakk>
            \<Longrightarrow> (\<exists> i \<in> X. infRs i X' X)"
proof -
  fix X :: "'a set"
  assume H1: "ccpo X"
  fix Y
  assume H2: "Y \<subseteq> X"
  assume H3: "Y \<noteq> {}"

  from H3 H2 have C: "consi {u \<in> X. u \<lesssim> Y} X" by(simp add: consi_def; blast)
  have "{u \<in> X. u \<lesssim> Y} \<subseteq> X" by(auto)
  from H1 C this ccpo_def have "\<exists> b \<in> X. supRs b {u \<in> X. u \<lesssim> Y} X" by(blast)
  then obtain b where HbinX: "b \<in> X" and Hbsup: "supRs b {u \<in> X. u \<lesssim> Y} X" by auto

  have infH1: " b \<lesssim> Y" proof
    fix y
    assume Hy: "y \<in> Y"
    from this have "y \<greatersim>  {u \<in> X. u \<lesssim> Y}" by auto
    from this Hbsup HbinX show "b \<le> y"
      by (meson H2 Hy subsetCE supRs_def)
  qed

  have infH2: "\<forall> b2 \<in> X. b2 \<lesssim> Y \<longrightarrow> b2 \<le> b" proof
    fix b2
    assume Hb2: "b2 \<in> X"
    show "b2 \<lesssim> Y \<longrightarrow> b2 \<le> b" proof
      assume H: "b2 \<lesssim> Y"
      from this Hb2 have "b2 \<in> {u \<in> X. u \<lesssim> Y}" by auto
      from this Hbsup show "b2 \<le> b" by (simp add: supRs_def)
    qed
  qed

  show "(\<exists>i\<in>X. infRs i Y X)" proof
    from HbinX show "b \<in> X" by auto
  next
    from HbinX infH1 infH2 show "infRs b Y X" by (simp add: infRs_def)
  qed
qed

lemma greatest_element_implies_complete_lattice:
"\<lbrakk> ccpo (X :: ('a::order) set); \<exists> g \<in> X. g \<greatersim> X\<rbrakk> \<Longrightarrow> complete_latticeR X"
proof -
  fix X :: "'a set"
  assume H1: "ccpo X"
  assume H2: " \<exists> g \<in> X. g \<greatersim> X"
  from H2 obtain g where Hg1: "g \<in> X" and Hg2: " g \<greatersim> X" by auto

  have "(\<forall> X' \<subseteq> X. (\<exists> s \<in> X. infRs s X' X))" proof
    fix X'
    show " X' \<subseteq> X \<longrightarrow> (\<exists>s\<in>X. infRs s X' X)" proof
      assume H3:  "X' \<subseteq> X"
      have A1: "(X' = {}) \<longrightarrow> (\<exists>s\<in>X. infRs s X' X)" proof
        assume H4: "X' = {}"
        show "\<exists>s\<in>X. infRs s X' X" proof
          show "infRs g X' X"
            by (simp add: Hg1 H4 Hg2 infRs_def)
        next
          from Hg1 show "g \<in> X" by auto
        qed
      qed
      have A2: "X' \<noteq> {} \<Longrightarrow> \<exists>s\<in>X. infRs s X' X"
        by (simp add: ccpo_nonempty_has_inf H1 H3)

      from A1 A2 show "(\<exists>s\<in>X. infRs s X' X)" by auto
    qed
  qed
  from complete_lattice_iff_inf this show "complete_latticeR X" by auto
qed

lemma b3_ccpo: "ccpo {n3, t3, f3}" 
proof -
  have "\<forall>X' \<subseteq> {n3, t3, f3}.
       (consi X' {n3, t3, f3}) \<longrightarrow> (\<exists>b\<in>{n3, t3, f3}. supRs b X' {n3, t3, f3})" proof
    fix X' :: "bool3 set"
    show "X' \<subseteq> {n3, t3, f3} \<longrightarrow> (consi X' {n3, t3, f3}) \<longrightarrow>
       (\<exists>b\<in>{n3, t3, f3}. supRs b X' {n3, t3, f3})" proof
      assume H: "X' \<subseteq> {n3, t3, f3}"
      from bool3_set_cases have C: "X' = {} \<or> X' = {t3} \<or> X' = {f3} \<or> X' = {n3} \<or> X' = {t3, f3} \<or> X' = {t3, n3} \<or> X' = {f3, n3} \<or> X' = {t3, f3, n3}" by auto
      then show "(consi X' {n3, t3, f3}) \<longrightarrow> (\<exists>b\<in>{n3, t3, f3}. supRs b X' {n3, t3, f3})" proof
        assume "X' ={}"
        from this have "supRs n3 X' {n3, t3, f3}"
          by (simp add: less_eq_bool3_def supRs_def)
        from this show ?thesis by auto
      next
        assume "X' = {t3} \<or> X' = {f3} \<or> X' = {n3} \<or>X' = {t3, f3} \<or>
          X' = {t3, n3} \<or> X' = {f3, n3} \<or> X' = {t3, f3, n3}"
        then show ?thesis proof
        assume "X' = {t3}"
        from this have "supRs t3 X' {n3, t3, f3}" by (simp add: supRs_def)
        from this show ?thesis by auto
      next
        assume "X' = {f3} \<or> X' = {n3} \<or> X' = {t3, f3} \<or> X' = {t3, n3} \<or>
           X' = {f3, n3} \<or> X' = {t3, f3, n3}"
        then show ?thesis proof
          assume " X' = {f3}"
          from this have "supRs f3 X' {n3, t3, f3}" by (simp add: supRs_def)
          from this show ?thesis by auto
        next
          assume "X' = {n3} \<or> X' = {t3, f3} \<or> X' = {t3, n3} \<or> X' = {f3, n3} \<or>
              X' = {t3, f3, n3}"
          then show ?thesis proof
            assume "X' = {n3}"
            from this have "supRs n3 X' {n3, t3, f3}" by (simp add: supRs_def)
            from this show ?thesis by auto
          next
            assume " X' = {t3, f3} \<or> X' = {t3, n3} \<or> X' = {f3, n3} \<or> X' = {t3, f3, n3}"
            then show ?thesis proof
              assume "X' = {t3, f3}"
              from this have "\<not> consi X' {n3,t3,f3}" using C4 UNIV_bool3 by auto
              from this show ?thesis using UNIV_bool3 by blast
            next
              assume "X' = {t3, n3} \<or> X' = {f3, n3} \<or>X' = {t3, f3, n3}"
              then show ?thesis proof
                assume "X' = {t3, n3}"
                from this have "supRs t3 X' {n3, t3, f3}" using order_example1
                  by (simp add: insert_commute)
                from this show ?thesis by auto
              next
                assume "X' = {f3, n3} \<or> X' = {t3, f3, n3}"
                then show ?thesis proof
                  assume "X' = {f3, n3}"
                  from this have "supRs f3 X' {t3, n3, f3}" using order_example1B by blast
                  from this show ?thesis
                    by (simp add: insert_commute)
                next
                  assume "X' = {t3, f3, n3}"
                  from this have "\<not> consi X' {n3,t3,f3}" using C4 UNIV_bool3 by (simp add: consi_def; auto)
                  from this show ?thesis using UNIV_bool3 by blast
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed
  from this ccpo_def[of "{n3,t3,f3}"] show ?thesis by auto
qed

lemma b4_complete_lattice: "complete_latticeR {b4, n4, t4, f4}"
proof -
  have "(\<forall> X' \<subseteq> {b4, n4, t4, f4}. (\<exists> s \<in> {b4, n4, t4, f4}. supRs s X' {b4, n4, t4, f4}))" proof
    fix X' :: "bool4 set"
    show "X' \<subseteq> {b4, n4, t4, f4} \<longrightarrow> (\<exists>s\<in>{b4, n4, t4, f4}. supRs s X' {b4, n4, t4, f4})" proof
      assume HX': "X' \<subseteq> {b4, n4, t4, f4}"
      show "(\<exists>s\<in>{b4, n4, t4, f4}. supRs s X' {b4, n4, t4, f4})" proof
        show "supRs ( \<Squnion> X' ) X' {b4, n4, t4, f4}" proof-
          have Supp1: "\<Squnion> X' \<in> {b4, n4, t4, f4}" using bool4.exhaust by blast
          have Supp2: "\<Squnion> X' \<greatersim> X'" by (simp add: Sup_upper)
          have Supp3: "(\<forall> y \<in> {b4, n4, t4, f4}. y \<greatersim> X' \<longrightarrow> \<Squnion> X' \<le> y)"
            by (simp add: Sup_least)
          from Supp1 Supp2 Supp3 show ?thesis by (simp add: supRs_def)
        qed
      next
        show "\<Squnion> X' \<in> {b4, n4, t4, f4}" using bool4.exhaust by blast
      qed
    qed
  qed     
  from this show ?thesis using complete_lattice_iff_sup by blast
qed

lemma complete_lattice_ccpo: 
  fixes X ::"( 'a :: complete_lattice) set"
  assumes I:"X = UNIV"
  shows "ccpo X "
proof -
  have "\<forall>X'\<subseteq>X. consi X' X \<longrightarrow> (\<exists>b\<in>X. supRs b X' X)" proof
    fix X'
    show "X' \<subseteq> X \<longrightarrow> consi X' X \<longrightarrow> (\<exists>b\<in>X. supRs b X' X)" proof
      assume H: "X' \<subseteq> X"
      show "consi X' X \<longrightarrow> (\<exists>b\<in>X. supRs b X' X)" proof
        assume H2: "consi X' X"
        have "\<exists>b. supRs b X' X" proof
          have "(Sup X') \<in> X" using assms by blast
          then show "supRs (Sup X') X' X"
             by (simp add: Sup_least Sup_upper supRs_def)
         qed
         then show "\<exists>b\<in>X. supRs b X' X" using assms by blast
       qed
     qed
   qed
  then show ?thesis by (simp add: ccpo_def)
qed

lemma b4_ccpo: "ccpo {n4,t4,f4,b4}"
   by (simp add: UNIV_bool4 complete_lattice_ccpo)

lemma "\<not> ccpo {t2,f2}"
  using ccpo_least_element less_eq_bool2_def by fastforce

lemma above_sublattice_is_ccpo:
"\<lbrakk> ccpo (X :: ('a::order) set); x \<in> X \<rbrakk> \<Longrightarrow> ccpo {y \<in> X. x \<le> y}"
proof -
  fix X :: "('a ::order) set"
  assume H1: "ccpo X"
  fix x :: 'a
  assume HxinX: "x \<in> X"
  have "\<forall>X'\<subseteq>{y \<in> X. x \<le> y}. (consi X' {y \<in> X. x \<le> y}) \<longrightarrow> (\<exists> b \<in> {y \<in> X. x \<le> y}. supRs b X' {y \<in> X. x \<le> y})" proof
    fix X' ::"'a set"
    show "X'\<subseteq>{y \<in> X. x \<le> y} \<longrightarrow> (consi X' {y \<in> X. x \<le> y}) \<longrightarrow> (\<exists> b \<in> {y \<in> X. x \<le> y}. supRs b X' {y \<in> X. x \<le> y})" proof
      assume H2: "X'\<subseteq>{y \<in> X. x \<le> y}"
      show "(consi X' {y \<in> X. x \<le> y}) \<longrightarrow> (\<exists> b \<in> {y \<in> X. x \<le> y}. supRs b X' {y \<in> X. x \<le> y})" proof
        assume H3: "(consi X' {y \<in> X. x \<le> y})"
        from this have HX'1:"(consi X' X)" by(simp add: consi_def; auto)
        from H1 ccpo_def[of "X"] have H3:"\<forall>X'\<subseteq>X. consi X' X \<longrightarrow> (\<exists>b\<in>X. supRs b X' X)" by auto
        from H2 have HX'2: "X' \<subseteq> X" by auto
        from HX'1 HX'2 H3 have "\<exists> b \<in> X. supRs b X' X" by auto
        then obtain b where Hb1: "b \<in> X" and Hb2: "supRs b X' X" by auto
        show " \<exists>b\<in>{y \<in> X. x \<le> y}. supRs b X' {y \<in> X. x \<le> y}" proof(cases "X' = {}")
          case True
          show ?thesis proof
            have "x \<le> x" by auto
            from HxinX this show "x \<in> {y \<in> X. x \<le> y}" by simp
            then show " supRs x X' {y \<in> X. x \<le> y}" by (simp add: True supRs_def)
          qed
       next
         case False
         show ?thesis proof
           have "x \<le> b"
             by (metis (no_types, lifting) Ball_Collect False H2 Hb2 bot.extremum_uniqueI order_trans subset_emptyI supRs_def)
           from Hb2 this show "supRs b X' {y \<in> X. x \<le> y}" by (simp add: False supRs_def)
         next
           show "b \<in> {y \<in> X. x \<le> y}"
             by (metis (no_types, lifting) Collect_mem_eq Collect_mono_iff False H2 Hb1 Hb2 bot.extremum_uniqueI mem_Collect_eq order_trans subset_emptyI supRs_def)
         qed
       qed
     qed
   qed
 qed
  then show "ccpo {y \<in> X. x \<le> y}" by(simp add: ccpo_def)
qed

lemma below_sublattice_is_complete:
"\<lbrakk> ccpo (X :: ('a :: order) set); x \<in> X\<rbrakk> \<Longrightarrow> 
             complete_latticeR {z \<in> X. z \<le> x}"
proof-
  fix X :: "'a set"
  assume H1: "ccpo X"
  fix x :: 'a
  assume HxinX: "x \<in> X"
  have "\<forall>X'\<subseteq>{z \<in> X. z \<le> x}.(\<exists> i. i \<in> X \<and> i \<le> x \<and> infRs i X' {z \<in> X. z \<le> x})" proof
    fix X'
    show "(X'\<subseteq>{z \<in> X. z \<le> x}) \<longrightarrow> (\<exists>i. i \<in> X \<and> i \<le> x \<and> infRs i X' {z \<in> X. z \<le> x})" proof
      assume H2: "X'\<subseteq>{z \<in> X. z \<le> x}"
      show "(\<exists>i. i \<in> X \<and> i \<le> x \<and> infRs i X' {z \<in> X. z \<le> x})" proof(cases "X' = {}")
        case True
        show ?thesis proof
          from True have H3: "x \<lesssim> X' \<and> (\<forall>y\<in> {z \<in> X. z \<le> x}. y \<lesssim> X' \<longrightarrow> y \<le> x)" by simp
          show " x \<in> X \<and> x \<le> x \<and> infRs x X' {z \<in> X. z \<le> x}" proof
            from HxinX show "x \<in> X" by auto
          next
            show "x \<le> x \<and> infRs x X' {z \<in> X. z \<le> x}" proof
              show "x\<le>x" by auto
            next
              from HxinX H3 show "infRs x X' {z \<in> X. z \<le> x}" by (simp add: infRs_def)
            qed
          qed
        qed
      next
        case False
        from this H1 H2 ccpo_nonempty_has_inf[of "X" "X'"] have
              "\<exists>i\<in>X. infRs i X' X" by auto
        from this obtain i where Hi1: "i \<in>X" and Hi2: "infRs i X' X" by auto
        show ?thesis proof
          show " i \<in> X \<and> i \<le> x \<and> infRs i X' {z \<in> X. z \<le> x}" proof
            from Hi1 show "i \<in> X" by auto
          next
            show "i \<le> x \<and> infRs i X' {z \<in> X. z \<le> x}" proof
              from Hi2 infRs_def show "i \<le> x"
                by (metis (no_types, lifting) Ball_Collect False H2 bot.extremum_uniqueI order_trans subset_emptyI)
            next
              from Hi2 infRs_def have "i \<le> x"
                by (metis (no_types, lifting) Ball_Collect False H2 bot.extremum_uniqueI order_trans subset_emptyI)
              from Hi2 this show " infRs i X' {z \<in> X. z \<le> x}" by(simp add: infRs_def)
            qed
          qed
        qed
      qed
    qed
  qed
    from this show "complete_latticeR {z \<in> X. z \<le> x}" by(simp add: complete_lattice_iff_inf complete_latticeR_def)
  qed

definition SupFun :: "('a ::order) set \<Rightarrow> 'a set \<Rightarrow> 'a" where
"SupFun X Y = (if (consi X Y) then (SOME x. supRs x X Y) else undefined)"

lemma SupFun_inX: "\<lbrakk> ccpo (Y :: ('a :: order) set); (X:: 'a set) \<subseteq> Y;
                        consi X Y \<rbrakk> \<Longrightarrow> (SupFun X Y) \<in> Y"
proof -
  fix X Y :: \<open>'a set\<close>
  assume H1: "ccpo Y"
  assume H2: "X \<subseteq> Y"
  assume H3: "consi X Y"
  show "(SupFun X Y) \<in> Y" proof-
    have "(SOME x. (x \<in> Y) \<and> (\<forall>y\<in>X. y \<le> x) \<and> (\<forall>y\<in>Y. (\<forall>ya\<in>X. ya \<le> y) \<longrightarrow> x \<le> y)) \<in> Y" proof(rule someI2_ex)
      from H1 H2 H3 show "\<exists>a. a \<in> Y \<and> (\<forall>y\<in>X. y \<le> a) \<and> (\<forall>y\<in>Y. (\<forall>ya\<in>X. ya \<le> y) \<longrightarrow> a \<le> y)"
        by(simp add: ccpo_def supRs_def) blast
    next
      show "\<And>x. x \<in> Y \<and> (\<forall>y\<in>X. y \<le> x) \<and> (\<forall>y\<in>Y. (\<forall>ya\<in>X. ya \<le> y) \<longrightarrow>
                 x \<le> y) \<Longrightarrow> x \<in> Y" by auto
    qed
    from H3 this have "(if consi X Y then (SOME x. supRs x X Y) else undefined) \<in> Y" by(simp add: supRs_def)
    then show "SupFun X Y \<in> Y" by(simp add: SupFun_def)
  qed
qed

lemma SupFun_greater: "\<lbrakk> ccpo (Y :: ('a :: order) set); (X:: 'a set) \<subseteq> Y;
                        consi X Y \<rbrakk> \<Longrightarrow> (SupFun X Y) \<greatersim> X"
proof -
  fix X Y :: \<open>'a set\<close>
  assume H1: "ccpo Y"
  assume H2: "X \<subseteq> Y"
  assume H3: "consi X Y"
  show "(SupFun X Y) \<greatersim> X" proof
    fix y
    show "y \<in> X \<Longrightarrow> y \<le> SupFun X Y" proof-
      assume H4: "y \<in> X"
      have "y \<le> (SOME x. (x \<in> Y) \<and> (\<forall>y\<in>X. y \<le> x) \<and> (\<forall>y\<in>Y. (\<forall>ya\<in>X. ya \<le> y) \<longrightarrow> x \<le> y)) " proof(rule someI2_ex)
        from H1 H2 H3 show "\<exists>a. (a \<in> Y) \<and> (\<forall>y\<in>X. y \<le> a) \<and> (\<forall>y\<in>Y. (\<forall>ya\<in>X. ya \<le> y) \<longrightarrow> a \<le> y)" by(simp add: ccpo_def supRs_def) blast
      next
        from H4 show "\<And>x. (x \<in> Y) \<and> (\<forall>y\<in>X. y \<le> x) \<and> (\<forall>y\<in>Y. (\<forall>ya\<in>X. ya \<le> y) \<longrightarrow> x \<le> y) \<Longrightarrow> y \<le> x" by auto
      qed
      from H3 this have "y \<le> (if consi X Y then (SOME x. supRs x X Y) else undefined)" by(simp add: supRs_def)
      then show "y \<le> SupFun X Y" by(simp add: SupFun_def)
    qed
  qed
qed

lemma SupFun_least: "\<lbrakk> ccpo (Y :: ('a :: order) set); (X:: 'a set) \<subseteq> Y;
                        consi X Y\<rbrakk> \<Longrightarrow> (\<And> y. y \<in> Y \<Longrightarrow> y \<greatersim> X \<Longrightarrow> (SupFun X Y) \<le> y)"
proof -
  fix X Y :: \<open>'a set\<close> fix y :: 'a
  assume H1: "ccpo Y"
  assume H2: "X \<subseteq> Y"
  assume H3: "consi X Y"
  show "(\<And> y. y \<in> Y \<Longrightarrow> y \<greatersim> X \<Longrightarrow> (SupFun X Y) \<le> y)" proof-
      have "(\<And> y. y \<in> Y \<Longrightarrow> y \<greatersim> X \<Longrightarrow> (SOME x. (x \<in> Y) \<and> (\<forall>y\<in>X. y \<le> x) \<and> (\<forall>y\<in>Y. y \<greatersim> X \<longrightarrow> x \<le> y)) \<le> y) " proof(rule someI2_ex)
        from H1 H2 H3 show " \<And>y. y \<in> Y \<Longrightarrow> \<forall>ya\<in>X. ya \<le> y \<Longrightarrow> \<exists>a. (a \<in> Y) \<and> (\<forall>y\<in>X. y \<le> a) \<and>
             (\<forall>y\<in>Y.(\<forall>ya\<in>X. ya \<le> y) \<longrightarrow> a \<le> y)" by(simp add: ccpo_def supRs_def) blast
      next
        show " \<And>y x. y \<in> Y \<Longrightarrow> \<forall>ya\<in>X. ya \<le> y \<Longrightarrow> x \<in> Y \<and> (\<forall>y\<in>X. y \<le> x) \<and>
           (\<forall>y\<in>Y. (\<forall>ya\<in>X. ya \<le> y) \<longrightarrow> x \<le> y) \<Longrightarrow> x \<le> y" by simp
      qed
      from H3 this have "(\<And> y. y \<in> Y \<Longrightarrow> y \<greatersim> X \<Longrightarrow> (if consi X Y then SOME x. supRs x X Y else undefined) \<le> y)" by(simp add: supRs_def)
      then show "(\<And> y. y \<in> Y \<Longrightarrow> y \<greatersim> X \<Longrightarrow> SupFun X Y \<le> y)" by(simp add: SupFun_def)
    qed
  qed

lemma SupFun_is_sup: "\<lbrakk> ccpo (Y :: ('a :: order) set); (X:: 'a set) \<subseteq> Y;
                        consi X Y \<rbrakk> \<Longrightarrow> supRs (SupFun X Y) X Y"
  by (simp add: SupFun_greater SupFun_least SupFun_inX supRs_def)

abbreviation "pot X \<equiv> {f :: ('d \<Rightarrow> 'a). range f \<subseteq> X}"

lemma function_space_ccpo:
"\<lbrakk> ccpo (X :: ('a :: order) set)\<rbrakk> \<Longrightarrow> ccpo (pot X)"
proof-
  fix X :: "'a set"
  assume Hccpo: "ccpo X"
  then have H1: "\<forall>X'\<subseteq>X. consi X' X \<longrightarrow> (\<exists>b\<in>X. supRs b X' X)" by (simp add: ccpo_def)
  have "\<forall> F \<subseteq>  pot X. consi F (pot X) \<longrightarrow> (\<exists> f \<in>  pot X. supRs f F (pot X) )"
  proof
    fix F :: "('d \<Rightarrow> 'a) set"
    show " F \<subseteq> pot X \<longrightarrow> consi F (pot X) \<longrightarrow> (\<exists>f\<in>pot X. supRs f F (pot X))" proof
      assume H2: " F \<subseteq> pot X"
      show "consi F (pot X) \<longrightarrow> (\<exists>f\<in>pot X. supRs f F (pot X))" proof
        assume H3: "consi F (pot X)"
        let ?fd = \<open>(\<lambda>d. SupFun {y. \<exists>f\<in>F. y = f d} X)\<close>
        show "(\<exists>f\<in>pot X. supRs f F (pot X))" proof

          have Sconsid: "\<And> d. consi {y. \<exists>f\<in>F. y = f d} X" proof -
            fix d :: 'd
            have "\<And>x y. (\<exists>f\<in>F. x = f d) \<Longrightarrow> (\<exists>f\<in>F. y = f d) \<Longrightarrow> (\<exists>b\<in>X. x \<le> b \<and> y \<le> b)" proof-
              fix x
              fix y
              assume "(\<exists>f\<in>F. x = f d)"
              then obtain fx where Hfx1: "fx \<in> F" and Hfx2: "x = fx d" by auto
              assume "(\<exists>f\<in>F. y = f d)"
              then obtain fy where Hfy1: "fy \<in> F" and Hfy2: "y = fy d" by auto
              from H3 Hfx1 Hfy1 consi_def[of "F" "pot X"] have "\<exists> fbound. range fbound \<subseteq> X \<and> fx \<le> fbound \<and> fy \<le> fbound" by simp
              then obtain fbound where Hfbound1: "range fbound \<subseteq> X" and Hfbound2: "fx \<le> fbound" and Hfbound3: "fy \<le> fbound" by auto
              show "(\<exists>b\<in>X. x \<le> b \<and> y \<le> b)" proof
                from Hfbound2 Hfbound3 have "fx d \<le> fbound d \<and> fy d \<le> fbound d"
                  by (simp add: le_funD)
                then show "x \<le> fbound d \<and> y \<le> fbound d" by(simp add: Hfx2 Hfy2)
              next
                from Hfbound1 show "fbound d \<in> X" by auto
              qed
            qed
            then show "consi {y. \<exists>f\<in>F. y = f d} X" by(simp add: consi_def)
          qed

          have SsupRs:"\<And> d. supRs (SupFun {y. \<exists>f\<in>F. y = f d} X) {y. \<exists>f\<in>F. y = f d} X" proof -
             fix d :: 'd
             from Sconsid[of "d"] Hccpo SupFun_is_sup[of "X" "{y. \<exists>f\<in>F. y = f d}"]
             show "supRs (SupFun {y. \<exists>f\<in>F. y = f d} X) {y. \<exists>f\<in>F. y = f d} X"
               using H2 by blast
           qed
          
           show "supRs ?fd F (pot X)" proof-
             have " (?fd \<in> pot X) \<and> (\<forall>f\<in>F. f \<le> (\<lambda>d. SupFun {y. \<exists>f\<in>F. y = f d} X) ) \<and>
              (\<forall>f. range f \<subseteq> X \<longrightarrow> (\<forall>ya\<in>F. ya \<le> f) \<longrightarrow> (\<lambda>d. SupFun {y. \<exists>f\<in>F. y = f d} X) \<le> f)" proof
               show "?fd \<in> pot X"
                 by (metis (no_types, lifting) SsupRs image_subset_iff mem_Collect_eq supRs_def)
             next
               show "(\<forall>f\<in>F. f \<le> (\<lambda>d. SupFun {y. \<exists>f\<in>F. y = f d} X) ) \<and>
              (\<forall>f. range f \<subseteq> X \<longrightarrow> (\<forall>ya\<in>F. ya \<le> f) \<longrightarrow> (\<lambda>d. SupFun {y. \<exists>f\<in>F. y = f d} X) \<le> f)" proof
               show " \<forall>f\<in>F. f \<le> (\<lambda>d. SupFun {y. \<exists>f\<in>F. y = f d} X)" proof
                 fix f
                 assume Hf: "f \<in> F"
                 from SsupRs have "\<And> d. (SupFun {y. \<exists>f\<in>F. y = f d} X) \<greatersim> {y. \<exists>f\<in>F. y = f d}" by(simp add: supRs_def)
                 from this Hf have "\<And> d. f d \<le> SupFun {y. \<exists>f\<in>F. y = f d} X" by auto
                 from this show "f \<le> (\<lambda>d. SupFun {y. \<exists>f\<in>F. y = f d} X)" by (simp add: le_funI)
               qed
             next
               show "(\<forall>f. range f \<subseteq> X \<longrightarrow> (\<forall>ya\<in>F. ya \<le> f) \<longrightarrow> (\<lambda>d. SupFun {y. \<exists>f\<in>F. y = f d} X) \<le> f)" proof
                 fix f :: "'d \<Rightarrow> 'a"
                 show "(range f \<subseteq> X \<longrightarrow> (\<forall>ya\<in>F. ya \<le> f) \<longrightarrow> (\<lambda>d. SupFun {y. \<exists>f\<in>F. y = f d} X) \<le> f)" proof
                   assume Hf1: "range f \<subseteq> X"
                   show "(\<forall>ya\<in>F. ya \<le> f) \<longrightarrow> (\<lambda>d. SupFun {y. \<exists>f\<in>F. y = f d} X) \<le> f" proof
                     assume Hf2: "(\<forall>ya\<in>F. ya \<le> f)"
                     have "\<And> d. (SupFun {y. \<exists>f\<in>F. y = f d} X) \<le> (f d)" proof-
                       fix d :: 'd
                       from Hf1 Hf2 SsupRs[of "d"] supRs_def[of "(SupFun {y. \<exists>f\<in>F. y = f d} X)" "{y. \<exists>f\<in>F. y = f d}" "X"]
                       show "(SupFun {y. \<exists>f\<in>F. y = f d} X) \<le> f d "
                         by (smt le_funD mem_Collect_eq rangeI subsetCE)
                     qed
                     from this show "(\<lambda>d. SupFun {y. \<exists>f\<in>F. y = f d} X) \<le> f" by(simp add: le_funI)
                   qed
                 qed
               qed
             qed
           qed
           from this show ?thesis by(simp add: supRs_def)
         qed
       
          have fdprop: "?fd \<in> pot X"
            by (metis (no_types, lifting) SsupRs image_subset_iff mem_Collect_eq supRs_def)

          from this have "\<forall> d :: 'd. ?fd(d) \<in> X" by auto
          from this supRs_def show "?fd \<in> pot X" by auto
        qed
           qed
         qed
       qed
  then show "ccpo (pot X)" by (simp add:ccpo_def)
qed

lemma function_space_ccpo_full:
" ccpo (UNIV :: ( ('a ::order) set) ) \<Longrightarrow> ccpo (UNIV :: ('d \<Rightarrow> 'a) set) "
  using  function_space_ccpo by fastforce

lemma function_space_ccpo_bool3:
" ccpo (UNIV :: ('d \<Rightarrow> bool3) set) "
  by (simp add: function_space_ccpo_full UNIV_bool3 b3_ccpo)

lemma function_space_ccpo_bool4:
" ccpo (UNIV :: ('d \<Rightarrow> bool4) set) "
  by (simp add: function_space_ccpo_full UNIV_bool4 b4_ccpo)

lemma function_space_complete_lattice:
"\<lbrakk> complete_latticeR (X :: ('a :: order) set)\<rbrakk> \<Longrightarrow> complete_latticeR (pot X)"
proof-
  fix X :: "('a :: order) set"
  assume H: "complete_latticeR X"
  then have "\<exists> x \<in> X. infRs x {} X" by(simp add:complete_latticeR_def)
  then obtain x where Hx1: "x \<in> X" and Hx2: "infRs x {} X" by auto
  from Hx2 have Hxupperbound: "x \<greatersim> X" by(simp add: infRs_def)
  let ?fx = "(\<lambda> d. x)"
  from Hxupperbound have Hfxupperbound: " ?fx \<greatersim> pot X" using le_fun_def by fastforce

  from Hx1 have Hfx1: "?fx \<in> (pot X)" by auto

  from H have "ccpo X" by(simp add: ccpo_def complete_latticeR_def)
  then have "ccpo (pot X)" using function_space_ccpo by auto
  from this H Hfxupperbound Hfx1 show "complete_latticeR (pot X)"
    using greatest_element_implies_complete_lattice[of "pot X"] by blast
qed

lemma function_space_complete_lattice_full:
"complete_latticeR (UNIV :: ('a :: order) set) \<Longrightarrow> complete_latticeR (UNIV :: ('d \<Rightarrow> 'a) set)"
  using function_space_complete_lattice by fastforce

lemma function_space_complete_lattice_bool4:
" complete_latticeR (UNIV :: ('d \<Rightarrow> bool4) set) "
  using UNIV_bool4 b4_complete_lattice
  by (simp add: function_space_complete_lattice_full insert_commute)

definition soundp:: "('a :: order) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
"soundp x f \<equiv> (x \<le> f x)"

definition repletep:: "('a :: order) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
"repletep x f \<equiv> (f x \<le> x)"

definition fixedp :: "('a :: order) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
"fixedp x f \<equiv> ( x = f x)"

abbreviation monot where
"monot (f :: (('a ::order) \<Rightarrow> 'a)) \<equiv>
     ( \<forall> a :: 'a. \<forall> b :: 'a. a \<le> b \<longrightarrow> f a \<le> f b) "

lemma max_elem_in_ccpo:
" \<lbrakk> ccpo (X :: ('a :: order) set); x \<in> X \<rbrakk>
    \<Longrightarrow> \<exists> m \<in> X. ( \<forall> a \<in> X. m \<le> a \<longrightarrow> m = a) \<and> x \<le> m"
proof-
  fix X :: "('a ::order) set"
  fix x :: 'a
  assume H1: "ccpo X"
  assume H2: "x \<in> X"
  let ?Y = "{y \<in> X. x \<le> y}"
  from H1 H2 have H3: "ccpo ?Y" using above_sublattice_is_ccpo by auto

  let ?r = "{ ((a :: 'a), (b::'a) ) . a \<in> ?Y \<and> b \<in> ?Y \<and>  a \<le> b}"
  have "x \<le> x" by auto
  from this have Hf: "Field ?r = ?Y" by(simp add: Field_def; auto)
  have Hr: "refl_on ?Y ?r" by (simp add: refl_on_def')
  have Ha: "antisym ?r" by (simp add: antisym_def; auto)
  have Ht: "trans ?r" by (simp add: trans_def; auto)
  from Hf Hr Ha Ht have Hpo: "Partial_order ?r"
    by (simp add: partial_order_on_def preorder_on_def)

  have "\<forall>C\<in>Chains ?r. \<exists>u\<in>Field ?r. \<forall>a\<in>C. (a, u) \<in> ?r" proof
    fix C :: "'a set"
    assume HC: "C \<in> Chains ?r"
    from this have HCss: "C \<subseteq> ?Y" by (simp add: Chains_def; auto)

    from HC have "\<forall> a \<in> C . \<forall> b \<in> C. a \<le> b \<or> b \<le> a" by(simp add: Chains_def; auto)
    from this have "\<forall> a \<in> C . \<forall> b \<in> C. \<exists> u \<in> C. a \<le> u \<and> b \<le> u" by auto
    from HCss this consi_def[of "C" "?Y"] have "consi C ?Y" by blast
    from this H3 ccpo_def[ of "?Y"] have "(\<exists>b\<in>?Y. supRs b C ?Y)" using HCss by blast
    then obtain b where Hb1: "b\<in> ?Y" and Hb2: "supRs b C ?Y" by auto
    from Hb2 supRs_def have "b \<greatersim> C" by auto

    from Hb1 this have "\<exists> u \<in> ?Y. u \<greatersim> C" by auto
    from this Hf HCss show "\<exists>u\<in>Field ?r. \<forall>a\<in>C. (a, u) \<in> ?r" by auto
  qed

  from Hf Hpo Zorns_po_lemma[of "?r"] this have "\<exists>m\<in>?Y. \<forall>a\<in>?Y. m \<le> a \<longrightarrow> a = m" by simp
  from this show " \<exists> m \<in> X. ( \<forall> a \<in> X. m \<le> a \<longrightarrow> m = a) \<and> x \<le> m"
    by (metis (mono_tags, lifting) mem_Collect_eq order_trans)
qed

lemma soundp_implies_fixedp:
" \<lbrakk> ccpo (X :: ('a ::order) set); x \<in> X; soundp x f; monot (f :: ('a \<Rightarrow> 'a)); f`X \<subseteq> X \<rbrakk> 
     \<Longrightarrow> \<exists> z \<in> X. x \<le> z \<and> fixedp z f"
proof-
  fix X :: "'a set" fix x :: 'a
  assume H1: " ccpo X" assume H2: "x \<in> X"
  fix f:: "'a \<Rightarrow> 'a"
  assume H3: "soundp x f" assume H4: "monot f" assume Himgf: "f`X \<subseteq> X"

  let ?Y = "{ y \<in> X. soundp y f \<and> x \<le> y}"
  have "ccpo ?Y" proof-
    have " \<forall>X'\<subseteq>?Y. consi X' ?Y \<longrightarrow> (\<exists>b. b \<in> ?Y \<and> supRs b X' ?Y) " proof
      fix Z :: "'a set"
      show "Z\<subseteq>?Y \<longrightarrow> consi Z ?Y \<longrightarrow> (\<exists>b. b \<in> ?Y \<and> supRs b Z ?Y)" proof
        assume H5: "Z\<subseteq>?Y"
        show "consi Z ?Y \<longrightarrow> (\<exists>b. b \<in> ?Y \<and> supRs b Z ?Y)" proof(cases "Z={}")
          case True
          have "(\<exists>b. b \<in> ?Y \<and> supRs b Z ?Y)" proof
            have "x \<in> ?Y \<and> supRs x {} ?Y" by (simp add: H2 H3 supRs_def)
            from this True show "x \<in> ?Y \<and> supRs x Z ?Y" by auto
          qed
          from this show ?thesis by auto
        next
          case False
          show "consi Z ?Y \<longrightarrow> (\<exists>b. b \<in> ?Y \<and> supRs b Z ?Y)" proof
          assume H6: "consi Z ?Y"
            have HYssX: " ?Y \<subseteq> X" by blast
            from this H6 have Hzconsi: "consi Z X" using consi_subset by blast
            from HYssX and H5 have "Z \<subseteq> X" by auto
            from this Hzconsi H1 ccpo_def[of X] have "(\<exists>b\<in>X. supRs b Z X)" by auto
            then obtain b where Hb1: "b \<in> X" and Hb2: "supRs b Z X" by auto
            from Hb2 H2 have HbgrZ: "b \<greatersim> Z" by (simp add: supRs_def)
            from this False have Hbgreaterx: "b \<ge> x"
              by (metis (no_types, lifting) Ball_Collect H5 atLeastAtMost_iff atLeastatMost_empty_iff bot.extremum_uniqueI empty_iff subset_emptyI)
            have Hbsound: "soundp b f" proof-
              have Hfbub: "f b \<greatersim> Z" proof
                fix z
                assume HzinZ:"z \<in> Z"
                from this have "z \<le> b" using HbgrZ by blast
                from this H4 have Hord: "f z \<le> f b " by auto
                from HzinZ H5 soundp_def[of "z" "f"] have "z \<le> f z" by blast
                from this Hord show "z \<le> f b" by auto
              qed
              from Himgf H2 have HbinX: "f b \<in> X"
                using Hb1 by blast
              from Hb2 have "(\<forall> y' \<in> X. y' \<greatersim> Z  \<longrightarrow> b \<le> y')" by (simp add: supRs_def)
              from this Hfbub HbinX have "b \<le> f b" by simp
              from this show ?thesis by(simp add: soundp_def)
            qed
            from Hb1 Hbgreaterx Hbsound have binY: "b \<in> ?Y" by auto

            have bisSup: "supRs b Z ?Y" proof-
              have Hsupb1: "b \<in> ?Y" using binY by auto
              have Hsupb2: "b \<greatersim> Z" using HbgrZ by auto
              from Hb2 have "\<forall> y \<in> X. y \<greatersim> Z \<longrightarrow> b \<le> y" by (simp add: supRs_def)
              from this have Hsupb3: "\<forall> y \<in> ?Y. y \<greatersim> Z \<longrightarrow> b \<le> y" by simp
              from Hsupb1 Hsupb2 Hsupb3 supRs_def[of "b" "Z" "?Y"] show ?thesis by(simp )
            qed
          show "(\<exists>b. b \<in> ?Y \<and> supRs b Z ?Y)" proof
            from binY bisSup show "b \<in> ?Y \<and> supRs b Z ?Y" by auto
          qed
        qed
      qed
    qed
  qed
    then show ?thesis by (simp add:ccpo_def)
  qed

  from this max_elem_in_ccpo[of "?Y" "x"] have
    "\<exists> m \<in> ?Y. (\<forall> a \<in> ?Y. m \<le> a \<longrightarrow> m = a) \<and> x \<le> m"
    using H2 H3 by blast
  from this obtain m where Hm1: "m \<in> ?Y" and Hm2: " (\<forall> a \<in> ?Y. m \<le> a \<longrightarrow> m = a)"
         and Hm3: "x \<le> m" by auto
  from Hm1 have "m \<le> f m" by(simp add: soundp_def)
  from this H4 have "f m \<le> f (f m)" by(simp)
  then have Hfsp: "soundp (f m) f" by(simp add: soundp_def)
  from Hm1 Himgf have HfminX: "(f m ) \<in> X" by auto
  from Hm3 \<open>m \<le> f m\<close> have "x \<le> f m " by auto
  from Hfsp this HfminX have "(f m) \<in> ?Y" by auto

  from this Hm2 \<open>m \<le> f m\<close> have "(f m) = m" by auto
  from this have "fixedp m f" by(simp add: fixedp_def)

  from Hm1 this Hm3 show "\<exists> z \<in> X. x \<le> z \<and> fixedp z f" by auto
qed

lemma soundp_repletep_implies_fixedp:
" \<lbrakk> ccpo (X :: ('a ::order) set); x \<in> X; y \<in> X; soundp x f;
  repletep y f; x \<le> y; monot (f :: ('a \<Rightarrow> 'a)); f`X \<subseteq> X \<rbrakk> 
     \<Longrightarrow> \<exists> z \<in> X. x \<le> z \<and> z \<le> y \<and> fixedp z f"
proof-
  fix X :: "('a ::order) set" fix x :: 'a fix y :: 'a
  assume H1: " ccpo X" assume H2: "x \<in> X" assume H3: "y \<in> X"
  fix f:: "'a \<Rightarrow> 'a"
  assume H4: "soundp x f" assume H5: "repletep y f"
  assume H6: "monot f" assume Himgf: "f`X \<subseteq> X"
  assume Hxy: "x \<le> y"

  let ?ZA = \<open>{z \<in> X. x \<le> z}\<close>
  from H1 H2 have "ccpo ?ZA" using above_sublattice_is_ccpo by auto

  let ?ZB = \<open>{z \<in> ?ZA. z \<le> y} \<close>
  from \<open>ccpo ?ZA\<close> H1 H3 Hxy have "complete_latticeR ?ZB"
    using below_sublattice_is_complete by blast
  then have "ccpo ?ZB" using complete_lattice_implies_ccpo by auto
  let ?Z = "{z \<in> X. x \<le> z \<and> z \<le> y}"
  from \<open>ccpo ?ZB\<close> have "ccpo ?Z" by simp
  from H2 Hxy have "x \<in> ?Z" by simp

  have "f` ?Z \<subseteq> ?Z" proof
    fix z'
    assume "z' \<in> f` ?Z"
    from this have "\<exists> x' \<in> ?Z. z' = f x'" by auto
    then obtain x' where Hx'1: "x' \<in> ?Z" and Hx'2:"z' = f x'" by auto

    from Hx'1 have "x \<le> x'" and "x' \<le> y" by auto
    from H6 have " f x \<le> f x'" using \<open>x \<le> x'\<close> by simp
    from H6 have " f x' \<le> f y" using \<open>x' \<le> y\<close> by simp

    from H4 soundp_def[of "x"]  \<open>f x \<le> f x'\<close> have \<open>x \<le> f x'\<close> by auto
    from H5 repletep_def[of "y"] \<open>f x' \<le> f y\<close> have \<open>f x' \<le> y\<close> by auto
    from Hx'1 Himgf have \<open>f x' \<in> X\<close> by auto
    from \<open>x \<le> f x'\<close> \<open>f x' \<le> y\<close> \<open>f x' \<in> X\<close> have \<open>f x' \<in> ?Z\<close> by simp
    from this Hx'2 show "z' \<in> ?Z" by auto
    qed

  from this \<open>ccpo ?Z\<close> \<open>x \<in> ?Z\<close> soundp_implies_fixedp[of "?Z" "x" "f"] H4 H6
  have "\<exists> p \<in> ?Z. fixedp p f \<and> x \<le> p" by simp
  then show \<open> \<exists> z \<in> X. x \<le> z \<and> z \<le> y \<and> fixedp z f\<close> by auto
qed

lemma repletep_implies_fixedp:
" \<lbrakk> ccpo (X :: ('a ::order) set); x \<in> X; repletep x f;
      monot (f :: ('a \<Rightarrow> 'a)); f`X \<subseteq> X \<rbrakk> 
     \<Longrightarrow> \<exists> z \<in> X. z \<le> x \<and> fixedp z f"
proof-
  fix X :: "'a set" fix x :: 'a
  assume H1: " ccpo X" assume H2: "x \<in> X"
  fix f:: "'a \<Rightarrow> 'a"
  assume H3: "repletep x f" assume H4: "monot f" assume Himgf: "f`X \<subseteq> X"
  from H1 have "\<exists> b \<in> X. b \<lesssim> X" using ccpo_least_element by auto
  then obtain b where Hb1: "b \<in> X" and Hb2: "b \<lesssim> X" by auto
  from H2 Hb2 have \<open>b \<le> x\<close> by auto
  from Hb2 Himgf have "b \<le> f b" using Hb1 by blast
  then have "soundp b f" by (simp add: soundp_def)
  from this soundp_repletep_implies_fixedp[of "X" "b" "x" "f"]
  show "\<exists> z \<in> X. z \<le> x \<and> fixedp z f" 
    using H1 H2 H3 H4 Hb1 Himgf \<open>b \<le> x\<close> by blast
qed

definition FixPs ::\<open>('a ::order) set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a set\<close>
where "FixPs X f = {x\<in> X. f(x) = x}"

lemma VisserFixp:
"\<lbrakk> ccpo (X:: ('a::order) set); monot (f :: 'a \<Rightarrow> 'a); f`X \<subseteq> X \<rbrakk>
      \<Longrightarrow> ccpo (FixPs X f)"
proof-
  fix X :: "('a :: order) set"
  fix f :: "'a \<Rightarrow> 'a"
  assume Hccpo: "ccpo X" assume Hmon: "monot f"
  assume Himgf: "f`X \<subseteq> X"
  show "ccpo (FixPs X f)" proof-
    have "\<forall> Y \<subseteq> (FixPs X f). consi Y (FixPs X f)
      \<longrightarrow> ( \<exists> b \<in> (FixPs X f). supRs b Y (FixPs X f))" proof
      fix Y
      show "Y \<subseteq> (FixPs X f) \<longrightarrow> consi Y (FixPs X f) \<longrightarrow> ( \<exists> b \<in> (FixPs X f). supRs b Y (FixPs X f))" proof
        assume \<open>Y \<subseteq> (FixPs X f)\<close>
        show "consi Y (FixPs X f) \<longrightarrow> ( \<exists> b \<in> (FixPs X f). supRs b Y (FixPs X f))" proof
          assume \<open>consi Y (FixPs X f)\<close>
    have "(FixPs X f) \<subseteq> X" using FixPs_def by auto
    from this \<open>consi Y (FixPs X f)\<close> have \<open>consi Y X\<close> using consi_subset by auto
    from this Hccpo ccpo_def[of "X"] have "(\<exists>b\<in>X. supRs b Y X)"
      using \<open>Y \<subseteq> FixPs X f\<close> \<open>FixPs X f \<subseteq> X\<close> by auto
    then obtain b where \<open>b \<in> X\<close> and \<open>supRs b Y X\<close> by auto
    from \<open>supRs b Y X\<close> have \<open>\<forall> y \<in> Y. y \<le> b\<close> using supRs_def by auto
    from \<open>Y \<subseteq> (FixPs X f)\<close> have \<open>\<forall> y \<in> Y. y = f y\<close>
      by (simp add: FixPs_def subset_eq)
    from this \<open>\<forall> y \<in> Y. y \<le> b\<close> have \<open>f b \<greatersim> Y\<close> using Hmon by fastforce
    from \<open>b \<in> X\<close> Himgf have \<open>f b \<in> X\<close> by auto
    from this \<open>f b \<greatersim> Y\<close> \<open>supRs b Y X\<close> have \<open>b \<le> f b\<close> by (simp add: supRs_def)
    from this have \<open>soundp b f\<close> using soundp_def by auto
  
    let ?Z = "{z \<in> X. f(z) = z \<and> b \<le> z}"
    from \<open>soundp b f\<close> soundp_implies_fixedp[of "X" "b" "f"]
     fixedp_def have \<open>?Z \<noteq> {}\<close> using Hccpo \<open>b \<in> X\<close> Hmon Himgf
      by (metis (mono_tags, lifting) empty_iff mem_Collect_eq)
    from Hccpo this ccpo_nonempty_has_inf[of "X" "?Z"]
    have "\<exists>i\<in> X. infRs i ?Z X" by auto
    from this obtain i where Hi1: "i \<in> X" and Hi2: \<open>infRs i ?Z X\<close> by auto
  
    have \<open>\<forall> z \<in> ?Z. f z = z\<close> by auto
    from Hi2 have "\<forall> z \<in> ?Z. i \<le> z" by(simp add: infRs_def)
    from this Hmon have "\<forall> z \<in> ?Z. f i \<le> f z" by blast
    from this \<open>\<forall> z \<in> ?Z. f z = z\<close> have \<open>f i \<lesssim> ?Z\<close>
      by (metis (no_types, lifting))
    from Hi1 Himgf have \<open>f i \<in> X\<close> by auto
    from \<open>f i \<in> X\<close> \<open>f i \<lesssim> ?Z\<close> Hi2 have \<open>f i \<le> i\<close> by(simp add: infRs_def)
    from this have \<open>repletep i f\<close> by(simp add: repletep_def)
  
    have \<open>b \<lesssim> ?Z\<close> by auto
    from \<open>b \<in> X\<close> this Hi2 have \<open>b \<le> i\<close> by(simp add: infRs_def)
  
    from this \<open>repletep i f\<close> \<open>soundp b f\<close> Hi1 \<open>b \<in> X\<close> Hmon Himgf Hccpo
    have \<open>\<exists>z\<in>X. b \<le> z \<and> z \<le> i \<and> fixedp z f\<close> using soundp_repletep_implies_fixedp[of "X" "b" "i" "f"]
      by auto
    then obtain b' where \<open>b' \<in> X\<close> and \<open>b \<le> b'\<close> and \<open>b' \<le> i\<close> and \<open>fixedp b' f\<close>
      by auto
    from \<open>fixedp b' f\<close> have \<open>f b' = b'\<close> by(simp add: fixedp_def)
    from this \<open>b \<le> b'\<close> \<open>b' \<in> X\<close> have "b' \<in> ?Z" by auto
    from \<open>supRs b Y X\<close> \<open>b \<le> b'\<close> have \<open>b' \<greatersim> Y\<close> by(simp add: supRs_def) auto
    from Hi2 \<open>b' \<le> i\<close> have \<open>b' \<lesssim> ?Z\<close> by(simp add: infRs_def) auto
  
    from \<open>fixedp b' f\<close> have \<open>f b' = b'\<close> by(simp add: fixedp_def)
    then have \<open>b' \<in> (FixPs X f)\<close> using \<open>b' \<in> X\<close> by(simp add: FixPs_def)
    have "\<forall>y\<in> (FixPs X f). ( y \<greatersim> Y  \<longrightarrow> b' \<le> y )" proof
        fix y
        assume \<open>y \<in> FixPs X f\<close>
        from this FixPs_def have \<open>f y = y\<close> by auto
        from \<open>y \<in> FixPs X f\<close> FixPs_def have \<open> y \<in> X\<close> by auto
        show " y \<greatersim> Y  \<longrightarrow> b' \<le> y " proof
          assume \<open>y \<greatersim> Y\<close>
          from this \<open> y \<in> X\<close> \<open>supRs b Y X\<close> have \<open>b \<le> y\<close> by(simp add: supRs_def)
          from this \<open>f y = y\<close> \<open> y \<in> X\<close> have \<open>y \<in> ?Z\<close> by auto
          from \<open>y \<in> ?Z\<close> \<open>b' \<lesssim> ?Z\<close> show \<open>b' \<le> y\<close> by auto
        qed
      qed

    from this \<open>b' \<greatersim> Y\<close> \<open>b' \<in> (FixPs X f)\<close> supRs_def[of "b'" "Y" "(FixPs X f)"]
    have \<open>supRs b' Y (FixPs X f)\<close> by simp
    then show "( \<exists> b \<in> (FixPs X f). supRs b Y (FixPs X f))"
      using \<open>b' \<in> (FixPs X f)\<close> by auto
  qed
qed
qed
  from this show ?thesis by(simp add: ccpo_def)
qed
qed

lemma VisserFixp2:
"\<lbrakk> ccpo (X:: ('a::order) set); monot (f :: 'a \<Rightarrow> 'a); f`X \<subseteq> X;
  \<exists> g \<in> X. g \<greatersim> X \<rbrakk>  \<Longrightarrow> \<exists> g' \<in> (FixPs X f). g' \<greatersim> (FixPs X f)"
proof-
  fix X :: "('a :: order) set"
  fix f :: "'a \<Rightarrow> 'a"
  assume Hccpo: "ccpo X" assume Hmon: "monot f"
  assume Himgf: "f`X \<subseteq> X" assume \<open>\<exists> g \<in> X. g \<greatersim> X\<close>
  then obtain g where Hg1: \<open>g \<in> X\<close> and Hg2: \<open>g \<greatersim> X\<close> by auto
  from Hg1 Hg2 have "consi (FixPs X f) X"
    by(simp add: consi_def FixPs_def) auto
  from ccpo_def[of "X"] have \<open>\<exists> b \<in> X. supRs b (FixPs X f) X\<close>
    by (metis (no_types, lifting) FixPs_def Hccpo \<open>consi (FixPs X f) X\<close> mem_Collect_eq subsetI)
  then obtain b where Hb1: \<open>b \<in> X\<close> and Hb2: "supRs b (FixPs X f) X" by auto
  from \<open>supRs b (FixPs X f) X\<close> have \<open>\<forall> y \<in> (FixPs X f). y \<le> b\<close> using supRs_def by auto
    have \<open>\<forall> y \<in> (FixPs X f). y = f y\<close> by (simp add: FixPs_def)
    from this \<open>\<forall> y \<in> (FixPs X f). y \<le> b\<close> have \<open>f b \<greatersim> (FixPs X f)\<close>
      using Hmon by fastforce
    from \<open>b \<in> X\<close> Himgf have \<open>f b \<in> X\<close> by auto
    from this \<open>f b \<greatersim> (FixPs X f)\<close> \<open>supRs b (FixPs X f) X\<close> have \<open>b \<le> f b\<close> by (simp add: supRs_def)
    then have \<open>soundp b f\<close> using soundp_def by auto
    from soundp_implies_fixedp[of "X" "b" "f"] \<open>b \<in> X\<close> \<open>soundp b f\<close>
      Hmon Himgf Hccpo have " \<exists>z\<in>X. b \<le> z \<and> fixedp z f" by auto
    from this obtain z where Hz1: \<open>z \<in> X\<close> and Hz2: \<open>b \<le> z\<close> and Hz3: \<open>fixedp z f\<close> by auto
    from Hz3 fixedp_def[of "z" "f"] have "(f z) = z" using sym by simp
    from Hz1 this have "z \<in> {x \<in> X. (f x) = x}" by simp
    from this FixPs_def[of "X" "f"] have \<open>z \<in> FixPs X f\<close> by auto
    show " \<exists> g' \<in> (FixPs X f). g' \<greatersim> (FixPs X f)" proof
      show \<open>z \<in> FixPs X f\<close> using \<open>z \<in> FixPs X f\<close> by auto
    next
      show "\<forall>y\<in>(FixPs X f). y \<le> z" proof
        fix y
        assume \<open> y \<in> (FixPs X f)\<close>
        from this \<open>supRs b (FixPs X f) X\<close> have \<open>y \<le> b\<close> by(simp add: supRs_def)
        from \<open>b \<le> z\<close> \<open>y \<le> b\<close> show \<open>y \<le> z\<close> by auto
      qed
    qed
  qed

lemma KnasterTarski:
"\<lbrakk> complete_latticeR (X:: ('a::order) set); monot (f :: 'a \<Rightarrow> 'a); f`X \<subseteq> X \<rbrakk>
      \<Longrightarrow> complete_latticeR (FixPs X f)"
proof-
  fix X :: "('a :: order) set"
  fix f :: "'a \<Rightarrow> 'a"
  assume Hcompl: "complete_latticeR X" assume Hmon: "monot f"
  assume Himgf: "f`X \<subseteq> X"
  from Hcompl complete_lattice_implies_ccpo have \<open>ccpo X\<close> by auto
  from this VisserFixp Hmon Himgf have \<open>ccpo (FixPs X f)\<close> by auto
  from Hcompl have "(\<exists>i\<in>X. infRs i {} X)" by (simp add: complete_latticeR_def)
  then obtain g where Hg1: \<open>g \<in> X\<close> and Hg2:\<open>infRs g {} X\<close> by auto
  from this have \<open>g \<greatersim> X\<close> by (simp add: infRs_def)

  from this Hmon Himgf \<open>ccpo X\<close> VisserFixp2 Hg1 have "\<exists>g'\<in>FixPs X f. g' \<greatersim> (FixPs X f)"
    by blast

  from this greatest_element_implies_complete_lattice
  show "complete_latticeR (FixPs X f)" using \<open>ccpo (FixPs X f)\<close> by blast
qed

definition IntrPs ::\<open>('a ::order) set \<Rightarrow> 'a set\<close>
where "IntrPs X = {x\<in> X. \<forall> y \<in> X. consi {x,y} X}"

lemma intrinsic_lattice:
"\<lbrakk> ccpo (X:: ('a::order) set) \<rbrakk>
      \<Longrightarrow> complete_latticeR (IntrPs X)"
proof-
  fix X ::\<open> 'a set\<close>
  assume \<open>ccpo X\<close>

  have \<open>\<forall> Y \<subseteq> (IntrPs X). \<exists> b \<in> (IntrPs X). supRs b Y (IntrPs X)\<close> proof
    fix Y :: \<open> 'a set\<close>
    show \<open>Y \<subseteq> (IntrPs X) \<longrightarrow> ( \<exists> b \<in> (IntrPs X). supRs b Y (IntrPs X))\<close> proof
      assume \<open>Y \<subseteq> (IntrPs X)\<close>
      then have \<open>Y \<subseteq> X\<close> using IntrPs_def by auto

      have \<open>consi Y X\<close> proof-
        have "\<forall> x \<in> Y. \<forall> y \<in> Y. \<exists> b \<in> X. x \<le> b \<and> y \<le> b" proof
          fix x assume \<open>x \<in> Y\<close> show " \<forall> y \<in> Y. \<exists> b \<in> X. x \<le> b \<and> y \<le> b" proof
            fix y assume \<open>y \<in> Y\<close> 
            from \<open>Y \<subseteq> (IntrPs X)\<close> \<open>x \<in> Y\<close> have \<open>x \<in> (IntrPs X)\<close> by auto
              from \<open>y \<in> Y\<close> \<open>Y \<subseteq> X\<close> have \<open>y \<in> X\<close> by auto
              from this \<open>x \<in> (IntrPs X)\<close> have \<open>consi {x,y} X\<close> by(simp add: IntrPs_def)
              from \<open>consi {x,y} X\<close> \<open>ccpo X\<close> ccpo_def
                obtain b where \<open>b \<in> X\<close> and \<open>supRs b {x,y} X\<close>
                  by (metis \<open>Y \<subseteq> X\<close> \<open>x \<in> Y\<close> \<open>y \<in> X\<close> empty_subsetI insert_subset subsetCE)
            show " \<exists> b \<in> X. x \<le> b \<and> y \<le> b" proof
              show "b \<in> X" using \<open>b \<in> X\<close> by auto
            next
              show "x\<le> b \<and> y \<le> b" using \<open>supRs b {x,y} X\<close> by (simp add: supRs_def)
            qed
          qed
        qed
        from this show ?thesis by(simp add: consi_def)
      qed
      from this \<open>ccpo X\<close> \<open>Y \<subseteq> X\<close> obtain b where \<open>b \<in> X\<close> and \<open>supRs b Y X\<close> using ccpo_def
        by (blast)

      have \<open>\<forall> x \<in> X. consi {b, x} X\<close> proof
        fix x assume \<open>x \<in> X\<close>

        have "(\<forall>x'\<in>Y \<union> {x}. \<forall>y'\<in>Y \<union> {x}. \<exists>b\<in>X. x' \<le> b \<and> y' \<le> b)" proof
          fix x' assume \<open>x' \<in> Y \<union> {x}\<close>
          show "\<forall>y'\<in>Y \<union> {x}. \<exists>b\<in>X. x' \<le> b \<and> y' \<le> b" proof
            fix y' assume \<open>y' \<in> Y \<union> {x}\<close>
            show "\<exists>b\<in>X. x' \<le> b \<and> y' \<le> b" proof(cases \<open>y' \<in> Y\<close>)
              case True
              from True \<open>Y \<subseteq> (IntrPs X)\<close> have \<open>y' \<in> (IntrPs X)\<close> by auto
              from \<open>x' \<in> Y \<union> {x}\<close> \<open>Y \<subseteq> (IntrPs X)\<close> \<open>x \<in> X\<close> IntrPs_def[of "X"] have \<open>x' \<in> X\<close> by auto
              from this \<open>y' \<in> (IntrPs X)\<close> IntrPs_def[of "X"] have \<open>consi {x', y'} X\<close>
                by (simp add: insert_commute)
              from True \<open>Y \<subseteq> (IntrPs X)\<close> IntrPs_def[of "X"] have \<open>y' \<in> X\<close> by auto
              from \<open>consi {x', y'} X\<close> \<open>ccpo X\<close> \<open>x' \<in> X\<close> \<open>y' \<in> X\<close> ccpo_def[of "X"]
                 have \<open>\<exists>b\<in>X. supRs b {x', y'} X\<close> by simp
                 then obtain b' where \<open>b' \<in> X\<close> and \<open>supRs b' {x', y'} X\<close> by auto
                 show ?thesis proof
                   show \<open>b' \<in> X\<close> using \<open>b' \<in> X\<close> by auto
                   show \<open>x' \<le> b' \<and> y' \<le> b'\<close> using \<open>supRs b' {x', y'} X\<close>
                     supRs_def[of "b'" "{x', y'}" "X"] by simp
                 qed
            next
              case False
              from this \<open>y' \<in> Y \<union> {x}\<close> have \<open>y' = x\<close> by auto
              then show ?thesis proof(cases \<open>x' \<in> Y\<close>)
                case True
                from True \<open>Y \<subseteq> (IntrPs X)\<close> have \<open>x' \<in> (IntrPs X)\<close> by auto
                from \<open>x' \<in> Y \<union> {x}\<close> \<open>Y \<subseteq> (IntrPs X)\<close> \<open>x \<in> X\<close> IntrPs_def[of "X"] have \<open>x' \<in> X\<close> by auto
                from True \<open>y' =x \<close> \<open>x \<in> X\<close> have \<open>y' \<in> X\<close> by auto
                from this \<open>x' \<in> (IntrPs X)\<close> IntrPs_def[of "X"] have \<open>consi {x', y'} X\<close>
                  by simp
                from \<open>consi {x', y'} X\<close> \<open>ccpo X\<close> \<open>x' \<in> X\<close> \<open>y' \<in> X\<close> ccpo_def[of "X"]
                 have \<open>\<exists>b\<in>X. supRs b {x', y'} X\<close> by simp
                 then obtain b' where \<open>b' \<in> X\<close> and \<open>supRs b' {x', y'} X\<close> by auto
                 show ?thesis proof
                   show \<open>b' \<in> X\<close> using \<open>b' \<in> X\<close> by auto
                   show \<open>x' \<le> b' \<and> y' \<le> b'\<close> using \<open>supRs b' {x', y'} X\<close>
                     supRs_def[of "b'" "{x', y'}" "X"] by simp
                 qed
                next
                  case False
                  from this \<open>x' \<in> Y \<union> {x}\<close> have \<open>x' = x\<close> by auto
                  from \<open>x' = x\<close> \<open>y' = x\<close> \<open>x \<in> X\<close> show ?thesis by auto
                qed
              qed
            qed
          qed
          from this have \<open>consi (Y \<union> {x}) X\<close> by(simp add: consi_def)
          from \<open>x \<in> X\<close> \<open>Y \<subseteq> (IntrPs X)\<close> IntrPs_def have \<open>(Y \<union> {x}) \<subseteq> X\<close> by blast
          from this \<open>ccpo X\<close> ccpo_def \<open>consi (Y \<union> {x}) X\<close> have \<open>\<exists> b \<in> X. supRs b (Y \<union> {x}) X\<close> by blast
          then obtain z where \<open>z \<in> X\<close> and \<open>supRs z (Y \<union> {x}) X \<close> by auto
          from \<open>supRs z (Y \<union> {x}) X \<close> have \<open>z \<greatersim> Y\<close> by (simp add: supRs_def)
          from this \<open>supRs b Y X\<close> \<open>z \<in> X\<close> supRs_def[of "b" "Y" "X"]
          have \<open>z \<ge> b\<close> by simp
          from \<open>supRs z (Y \<union> {x}) X \<close> have \<open>z \<ge> x\<close> by (simp add: supRs_def)
          from \<open>z \<ge> x\<close> \<open>z \<ge> b\<close> have \<open>z \<greatersim> { x, b}\<close> by auto
        then show \<open>consi {b, x} X\<close> using consi_def[of "{b,x}" "X"]
          using \<open>z \<in> X\<close> by blast
      qed

      from \<open>b \<in> X\<close> this IntrPs_def[of "X"] have \<open>b \<in> IntrPs X\<close> by simp
      from \<open>supRs b Y X\<close> \<open>b \<in> IntrPs X\<close> have \<open>supRs b Y (IntrPs X)\<close>
        by (simp add: supRs_def IntrPs_def)

      show \<open>( \<exists> b \<in> (IntrPs X). supRs b Y (IntrPs X))\<close> proof
        show \<open>b \<in> IntrPs X\<close> using \<open>b \<in> IntrPs X\<close> by auto
      next
        show \<open>supRs b Y (IntrPs X)\<close> using \<open>supRs b Y (IntrPs X)\<close> by auto
      qed
    qed
  qed
  from this complete_lattice_iff_sup show \<open>complete_latticeR (IntrPs X)\<close> by auto
qed

lemma intrinsic_largest:
"\<lbrakk> ccpo (X:: ('a::order) set) \<rbrakk> \<Longrightarrow> \<exists> i \<in> (IntrPs X). i \<greatersim> (IntrPs X)"
proof-
  fix X :: "'a set" assume Hccpo: \<open>ccpo X\<close>
  then have "complete_latticeR (IntrPs X)" using intrinsic_lattice by auto
  then have "\<exists> i \<in> (IntrPs X). infRs i {} (IntrPs X)" by (simp add: complete_latticeR_def)
  then obtain i where \<open>i \<in> IntrPs X\<close> and \<open>infRs i {} (IntrPs X)\<close> by auto
  show "\<exists> i \<in> (IntrPs X). i \<greatersim> (IntrPs X)" proof
    from \<open>infRs i {} (IntrPs X)\<close> show " \<forall>y\<in>IntrPs X. y \<le> i" by(simp add:infRs_def)
    from \<open>i \<in> IntrPs X\<close> show \<open>i \<in> IntrPs X\<close> by auto
  qed
qed

definition MaxiPs ::\<open>('a ::order) set \<Rightarrow> 'a set\<close>
where "MaxiPs X = {x\<in> X. \<forall> y \<in> X. x \<le> y \<longrightarrow> x = y}"

lemma greatest_intrinsic_is_sup_maxH1:
"\<lbrakk> ccpo (X :: ('a ::order) set); i \<in> (IntrPs X); i \<greatersim> (IntrPs X) \<rbrakk>
   \<Longrightarrow> (i \<in> X \<and> infRs i (MaxiPs X) X)" proof-
  fix X :: \<open>('a ::order) set\<close> fix i
  assume \<open>ccpo X\<close> \<open>i \<in> (IntrPs X)\<close> \<open>i \<greatersim> (IntrPs X)\<close>
  show "(i \<in> X \<and> infRs i (MaxiPs X) X)" proof
    show \<open>i \<in> X\<close> using \<open>i \<in> (IntrPs X)\<close> IntrPs_def by blast
    have \<open>i \<lesssim> (MaxiPs X)\<close> proof
      fix m assume \<open>m \<in> MaxiPs X\<close> then have \<open>m \<in> X\<close> by(simp add:MaxiPs_def)
      from this \<open>i \<in> (IntrPs X)\<close> have \<open>consi {i, m} X\<close> by(simp add: IntrPs_def)
      from \<open>i \<in> X\<close> \<open>m \<in> X\<close> this \<open>ccpo X\<close> have \<open>\<exists>b\<in>X. supRs b {i,m} X\<close>
        by (simp add:ccpo_def)
      then obtain b where \<open>b \<in> X\<close> and \<open>supRs b {i,m} X\<close> by auto
      from this have \<open>i \<le> b\<close> by(simp add: supRs_def)
      from \<open>supRs b {i,m} X\<close> have \<open>m \<le> b\<close> by(simp add: supRs_def)
      from this \<open>m \<in> MaxiPs X\<close> \<open>b \<in> X\<close> have "m = b" by (simp add: MaxiPs_def)
      
      from this \<open>i \<le> b\<close> show \<open>i \<le> m\<close> by auto
    qed

    from max_elem_in_ccpo[of "X" "i"] \<open>ccpo X\<close> \<open>i \<in> X\<close> MaxiPs_def[of "X"]
       have "(MaxiPs X) \<noteq> {}" by auto
    from this \<open>ccpo X\<close> ccpo_nonempty_has_inf MaxiPs_def
    have "\<exists> j \<in> X. infRs j (MaxiPs X) X" by auto
    then obtain j where \<open>j \<in> X\<close> and \<open>infRs j (MaxiPs X) X\<close> by auto
    from \<open>infRs j (MaxiPs X) X\<close> \<open>i \<lesssim> (MaxiPs X)\<close> \<open>i \<in> X\<close>
    have \<open>i \<le> j\<close> by (simp add: infRs_def)

    have "\<forall> x \<in> X. consi {j, x} X" proof
      fix x assume \<open>x \<in> X\<close>
      from max_elem_in_ccpo[of "X" "x"] \<open>ccpo X\<close> \<open>x \<in> X\<close> have
         "\<exists>m\<in>X. (\<forall>a\<in>X. m \<le> a \<longrightarrow> m = a) \<and> x \<le> m" by auto
      from this obtain m where \<open>m \<in> X\<close> and \<open>(\<forall>a\<in>X. m \<le> a \<longrightarrow> m = a)\<close> and \<open>x \<le> m\<close> by auto
      from \<open>(\<forall>a\<in>X. m \<le> a \<longrightarrow> m = a)\<close> \<open>m \<in> X\<close> have \<open>m \<in> MaxiPs X\<close> by(simp add: MaxiPs_def)
      from \<open>infRs j (MaxiPs X) X\<close>  \<open>m \<in> MaxiPs X\<close> have \<open>j \<le> m\<close> by(simp add: infRs_def)
      from \<open>j \<le> m\<close> \<open>x \<le> m\<close> \<open>m \<in> X\<close> show "consi {j, x} X" using consi_def by blast
    qed

    from this IntrPs_def[of "X"] \<open>j \<in> X\<close> have \<open>j \<in> (IntrPs X)\<close> by simp
    from this \<open>i \<greatersim> (IntrPs X)\<close> have \<open>j \<le> i\<close> by(simp add: IntrPs_def)
    from \<open>i \<le> j\<close> \<open>j \<le> i\<close> have \<open>i = j\<close> by auto
    from this \<open>infRs j (MaxiPs X) X\<close> show "infRs i (MaxiPs X) X" by auto
  qed
qed

section \<open>Preliminary Matters (continued)\<close>

datatype ('function_type, 'constant_type) tm
= Var nat
| Const 'constant_type
| Fun 'function_type \<open>('function_type, 'constant_type) tm list\<close>

datatype ('function_type, 'constant_type, 'relation_type) fm
= Rel 'relation_type \<open>('function_type, 'constant_type) tm list\<close>
| Equ \<open>('function_type, 'constant_type) tm\<close> \<open>('function_type, 'constant_type) tm\<close>
| Fal
| And \<open>('function_type, 'constant_type, 'relation_type) fm\<close> \<open>('function_type, 'constant_type, 'relation_type) fm\<close>
| Neg \<open>('function_type, 'constant_type, 'relation_type) fm\<close>
| Forall nat \<open>('function_type, 'constant_type, 'relation_type) fm\<close>

fun freevar_tm :: "('a, 'b) tm \<Rightarrow> nat set" where
" freevar_tm (Var n) = { n }" |
" freevar_tm (Const b) = {} " |
" freevar_tm (Fun f_symb term_list) = \<Union> (set (map freevar_tm term_list) )"

fun freevar :: " ('a, 'b, 'c) fm \<Rightarrow> nat set" where
"freevar (Rel r_symb term_list) = \<Union> (set (map freevar_tm term_list) )" |
"freevar (Equ tm1 tm2) = (freevar_tm tm1) \<union> (freevar_tm tm2)" |
"freevar (And fm1 fm2) = (freevar fm1) \<union> (freevar fm2)" |
"freevar (Neg f) = (freevar f)" |
"freevar Fal = {}" |
"freevar (Forall m f) = (freevar f) - {m} "

fun contvar :: " ('a, 'b, 'c) fm \<Rightarrow> nat set" where
"contvar (Rel r_symb term_list) = \<Union> (set (map freevar_tm term_list) )" |
"contvar (Equ tm1 tm2) = (freevar_tm tm1) \<union> (freevar_tm tm2)" |
"contvar (And fm1 fm2) = (contvar fm1) \<union> (contvar fm2)" |
"contvar (Neg f) = (contvar f)" |
"contvar Fal = {}" |
"contvar (Forall m f) = (contvar f) \<union> {m} "

fun freevar_tmL :: "('a, 'b) tm \<Rightarrow> nat list" where
" freevar_tmL (Var n) = [ n ]" |
" freevar_tmL (Const b) = [] " |
" freevar_tmL (Fun f_symb term_list) = remdups ( concat (map freevar_tmL term_list) )"

lemma freevar_tm_id: \<open>set (freevar_tmL t) = freevar_tm t\<close>
  by(induction t; simp)

fun freevarL :: " ('a, 'b, 'c) fm \<Rightarrow> nat list" where
"freevarL (Rel r_symb term_list) = remdups (concat (map freevar_tmL term_list))" |
"freevarL (Equ tm1 tm2) = remdups ( concat[ (freevar_tmL tm1), (freevar_tmL tm2)] )" |
"freevarL (And fm1 fm2) = remdups ( concat[ (freevarL fm1), (freevarL fm2)] )" |
"freevarL (Neg f) = (freevarL f)" |
"freevarL Fal = []" |
"freevarL (Forall m f) = removeAll m (freevarL f) "

lemma freevar_id: \<open>set (freevarL f) = freevar f\<close>
  by(induction f; simp add: freevar_tm_id)

lemma freevar_contvar: "freevar f \<subseteq> contvar f"
  by(induction f; simp; auto)

definition sentence where
"sentence f1 \<equiv> (freevar f1 = {})"

type_synonym 'v assignment = "nat \<Rightarrow> 'v"
type_synonym ('v, 'a,'b,'c) const_mod = "'b \<Rightarrow> 'v"
type_synonym ('v, 'a,'b,'c) func_mod = "'a \<Rightarrow> ('v list) \<Rightarrow> 'v"
type_synonym ('v, 'a,'b,'c) rela_mod_tau = "'c \<Rightarrow> ('v list) \<Rightarrow> bool"
text \<open>The idea here is that the value of e.g. func\_mod Fsymb should be
   set to undefined in a case where the lenght of the argument (which is a list)
   does not correspond to the arity of Fsymb. Also, if some object
   of type 'v comes not from the domain set and is in the argument list,
   we expect undefined as image\<close>
text\<open>Rela\_mod\_tau is just how one would do it using the build-in bool type
   of isabelle. However, this is just a deadend example because there
   True $\leq$ False, which is undesired in our context. \<close>


text \<open>'v is the type of the domain D ; 'b is the type of constant symbols;
   'a is the type of function symbols; 'c is the type of relation symbols \<close>
type_synonym ('v, 'a,'b,'c) mod1
   = \<open>('v, 'a,'b,'c) const_mod \<times> ('v, 'a,'b,'c) func_mod \<times> ('v, 'a,'b,'c) rela_mod_tau\<close>

fun value_tm :: \<open>'v assignment \<Rightarrow> (('v, 'a,'b,'c) const_mod \<times> ('v, 'a,'b,'c) func_mod) \<Rightarrow> ('a, 'b) tm \<Rightarrow> 'v\<close> where
"(value_tm s (Cw, Fw) (Var n)) = (s n)" |
"(value_tm s (Cw, Fw) (Const c)) = (Cw c)" |
"(value_tm s (Cw, Fw) (Fun f_symb term_list))
      = (Fw f_symb (map (\<lambda> x. value_tm s (Cw, Fw) x) term_list))"

lemma value_tm_locdet: \<open>\<lbrakk> \<forall>m \<in> freevar_tm t. s1 m = s2 m \<rbrakk>
     \<Longrightarrow> value_tm s1 (Cw, Fw) t = value_tm s2 (Cw, Fw) t\<close>
  apply(induction t; simp) by (metis (mono_tags, lifting) map_eq_conv)

type_synonym ('v, 'a,'b,'c, 'mybool) rela_mod =
  "'c \<Rightarrow> ('v list) \<Rightarrow> 'mybool"

type_synonym ('v, 'a,'b,'c, 'mybool) model
   = \<open>'v set \<times> ('v, 'a,'b,'c) const_mod \<times> ('v, 'a,'b,'c) func_mod \<times> ('v, 'a,'b,'c, 'mybool) rela_mod\<close>

type_synonym ('v, 'mybool) scheme
   = \<open>'mybool \<times> 'mybool \<times> ('mybool \<Rightarrow> 'mybool) \<times> ('mybool \<Rightarrow> 'mybool \<Rightarrow> 'mybool) \<times> ( 'v set \<Rightarrow> ('v \<Rightarrow> 'mybool) \<Rightarrow> 'mybool)\<close>

(* fun value_fm :: \<open>'v assignment \<Rightarrow> ('v, 'a, 'b, 'c, 'mybool) model \<Rightarrow> 'mybool \<Rightarrow> 'mybool \<Rightarrow> ('mybool \<Rightarrow> 'mybool) \<Rightarrow> ('mybool \<Rightarrow> 'mybool \<Rightarrow> 'mybool) \<Rightarrow> (('mybool set) \<Rightarrow> 'mybool) \<Rightarrow> ('a, 'b, 'c) fm \<Rightarrow> 'mybool\<close> where *)
(* fun value_fm :: \<open>'v assignment \<Rightarrow> ('v, 'a, 'b, 'c, 'mybool) model \<Rightarrow> 'mybool \<Rightarrow> 'mybool \<Rightarrow> ('mybool \<Rightarrow> 'mybool) \<Rightarrow> ('mybool \<Rightarrow> 'mybool \<Rightarrow> 'mybool) \<Rightarrow> (('v \<Rightarrow> 'mybool) \<Rightarrow> 'mybool) \<Rightarrow> ('a, 'b, 'c) fm \<Rightarrow> 'mybool\<close> where *)
fun value_fm :: \<open>('v, 'mybool) scheme \<Rightarrow> 'v assignment \<Rightarrow> ('v, 'a, 'b, 'c, 'mybool) model \<Rightarrow> ('a, 'b, 'c) fm \<Rightarrow> 'mybool\<close> where
"value_fm (myFalse, myTrue, myNot, myAnd, myUni) w (D, Cw, Fw, Rw) Fal = myFalse" |
"value_fm (myFalse, myTrue, myNot, myAnd, myUni) w (D, Cw, Fw, Rw) (Rel r_symb term_list) = (Rw r_symb (map (\<lambda> x. value_tm w (Cw,Fw) x) term_list))" |
"value_fm (myFalse, myTrue, myNot, myAnd, myUni) w (D, Cw, Fw, Rw) (Equ tm1 tm2) = ( if (value_tm w (Cw,Fw) tm1 = value_tm w (Cw,Fw) tm2) then myTrue else myFalse)" |
"value_fm (myFalse, myTrue, myNot, myAnd, myUni) w (D, Cw, Fw, Rw) (And fm1 fm2) = ( myAnd (value_fm (myFalse, myTrue, myNot, myAnd, myUni) w (D, Cw,Fw,Rw) fm1) (value_fm (myFalse, myTrue, myNot, myAnd, myUni) w (D, Cw,Fw,Rw) fm2))" |
"value_fm (myFalse, myTrue, myNot, myAnd, myUni) w (D, Cw, Fw, Rw) (Neg f) = (myNot (value_fm (myFalse, myTrue, myNot, myAnd, myUni) w (D, Cw,Fw,Rw) f))" |
"value_fm (myFalse, myTrue, myNot, myAnd, myUni) w (D, Cw, Fw, Rw) (Forall m f) = ( myUni D ( \<lambda> v. value_fm (myFalse, myTrue, myNot, myAnd, myUni) (\<lambda> k. if k=m then v else w k) (D,Cw,Fw,Rw) f ) )" 
(* "value_fm w (Cw, Fw, Rw) myFalse myTrue myNot myAnd myUni (Forall m f) = ( myUni (\<lambda> v. ( value_fm (\<lambda> k. if k=m then v else w k) (Cw,Fw,Rw) myFalse myTrue myNot myAnd myUni f ) ) )" *)

fun \<tau>_not ::\<open>bool2 \<Rightarrow> bool2\<close> where
"\<tau>_not t2 = f2" |"\<tau>_not f2 = t2"

lemma \<tau>_not_monot: \<open>b1 \<le> b2 \<Longrightarrow> \<tau>_not b1 \<le> \<tau>_not b2\<close>
  by(cases "b1"; cases "b2"; simp add: less_eq_bool2_def)

fun \<tau>_and ::\<open>bool2 \<Rightarrow> bool2 \<Rightarrow> bool2\<close> where
\<open> \<tau>_and t2 t2 = t2\<close> | \<open> \<tau>_and _ _ = f2\<close>

lemma \<tau>_and_monot: \<open>\<lbrakk> a1 \<le> a2; b1 \<le> b2 \<rbrakk> \<Longrightarrow> \<tau>_and a1 b1 \<le> \<tau>_and a2 b2\<close>
by(cases "a1"; cases "a2"; cases "b1"; cases "b2"; simp add: less_eq_bool2_def)

fun \<tau>_forall ::\<open>('v set ) \<Rightarrow> ('v \<Rightarrow> bool2) \<Rightarrow> bool2\<close> where
\<open>(\<tau>_forall D f) = ( if (\<forall> v \<in> D. f v = t2) then t2 else f2) \<close>

lemma \<open> (\<lambda> x. n3) \<le> (\<lambda> x. t3) \<close>
  by (simp add: le_funI less_eq_bool3_def)

lemma \<open> \<not> (\<lambda> x. t2) \<le> (\<lambda> x. f2)\<close>
  by (meson le_funD leq2.simps(4) less_eq_bool2_def)

lemma \<tau>_forall_monot:
  \<open>(fb1 :: ('v \<Rightarrow> bool2)) \<le> (fb2 :: ('v \<Rightarrow> bool2))
      \<Longrightarrow> (\<tau>_forall D fb1) \<le> (\<tau>_forall D fb2)\<close>
  apply(cases "\<tau>_forall D fb1"; cases "\<tau>_forall D fb2"; simp add: less_eq_bool2_def le_fun_def)
  apply(smt bool2.exhaust image_cong leq2.simps(4) range_eq_singletonD)
  by (smt bool2.exhaust image_cong leq2.simps(3) range_eq_singletonD)
(*   metis (full_types) bool2.exhaust le_fun_def leq2.simps less_eq_bool2_def rang) *)

abbreviation \<tau> :: \<open>('v, bool2) scheme\<close>
  where \<open>\<tau> \<equiv> (f2, t2, \<tau>_not, \<tau>_and, \<tau>_forall)\<close>

fun \<mu>_not::\<open>bool3 \<Rightarrow> bool3\<close> where
\<open>\<mu>_not t3 = f3\<close> |
\<open>\<mu>_not f3 = t3\<close> |
\<open>\<mu>_not n3 = n3\<close>

lemma \<mu>_not_monot: \<open>b1 \<le> b2 \<Longrightarrow> \<mu>_not b1 \<le> \<mu>_not b2\<close>
  by (smt \<mu>_not.elims leq3.simps(2) leq3.simps(3) leq3.simps(4) leq3.simps(5) leq3.simps(6) leq3.simps(7) leq3.simps(8) leq3.simps(9) less_eq_bool3_def)

fun \<mu>_and::\<open>bool3 \<Rightarrow> bool3 \<Rightarrow> bool3\<close> where
\<open>\<mu>_and n3 _ = n3\<close> | \<open>\<mu>_and _ n3 = n3\<close> |
\<open>\<mu>_and t3 t3 = t3\<close> | \<open>\<mu>_and t3 f3 = f3\<close> |
\<open>\<mu>_and f3 t3 = f3\<close> | \<open>\<mu>_and f3 f3 = f3\<close>

lemma \<mu>_and_monot: \<open>\<lbrakk> fm1 \<le> fm2 ; g1 \<le> g2 \<rbrakk> \<Longrightarrow> \<mu>_and fm1 g1 \<le> \<mu>_and fm2 g2\<close>
  by(cases "fm1"; cases "fm2"; cases "g1"; cases "g2"; simp add:less_eq_bool3_def)

(*
fun \<mu>_forall :: \<open>bool3 set \<Rightarrow> bool3\<close> where
"\<mu>_forall B = ( if B \<noteq> {} then ( if B = {t3}
            then t3 else (if n3 \<in> B then n3 else f3) ) else undefined)"
*)

fun \<mu>_forall :: \<open>('v set) \<Rightarrow> ('v \<Rightarrow> bool3) \<Rightarrow> bool3\<close> where
"\<mu>_forall D f = ( if (\<forall> v \<in> D. f v= t3) then t3 else
       (if (\<exists> v \<in> D. f v= n3) then n3 else f3) )"

lemma \<mu>_forall_monot:\<open>f1 \<le> fm2 \<Longrightarrow> \<mu>_forall D f1 \<le> \<mu>_forall D fm2\<close>
  by(cases "\<mu>_forall D f1"; cases "\<mu>_forall D fm2"; simp add: less_eq_bool3_def;
   metis (full_types) bool3.exhaust le_fun_def leq3.simps less_eq_bool3_def)

lemma \<open>range f = {t3} \<Longrightarrow> \<mu>_forall D f = t3\<close> by auto
lemma \<open>f` D = {f3} \<Longrightarrow> \<mu>_forall D f = f3\<close>
  by (metis \<mu>_forall.simps bex_imageD insert_image leq3.simps(3) singletonI singleton_insert_inj_eq')
lemma \<open>f` D = {n3} \<Longrightarrow> \<mu>_forall D f = n3\<close>
  by (metis \<mu>_forall.simps bex_imageD insert_image leq3.simps(1) singletonI singleton_insert_inj_eq')
lemma \<open>f` D = {n3, t3} \<Longrightarrow> \<mu>_forall D f = n3\<close>
  using image_iff[of "n3"] by (metis \<mu>_forall.simps insertI1)

lemma \<open> f` D = {n3, f3} \<Longrightarrow> \<mu>_forall D f = n3\<close>
  using image_iff[of "n3"] by (metis \<mu>_forall.simps insertI1)

lemma \<open>f` D = {f3, t3} \<Longrightarrow> \<mu>_forall D f = f3\<close> proof-
  assume A: "f` D = {f3, t3}"
  from A have \<open>\<exists> v1 \<in> D. f v1 = f3\<close> using image_iff by fastforce
  then obtain v1 where 1: \<open>v1 \<in> D \<and> f v1 = f3\<close> by auto
  from A have \<open>\<exists> v2 \<in> D. f v2 = t3\<close> using image_iff by fastforce
  then obtain v2 where 2: \<open>v2 \<in> D \<and> f v2 = t3\<close> by auto

  from 1 have 3: "\<not> (\<forall> v \<in> D. f v= t3)" by fastforce
  from A have 4: "\<not> (\<exists> v \<in> D. f v= n3)"
    by (metis (mono_tags, lifting) bool3.distinct(1) bool3.simps(4) insert_absorb insert_iff insert_image singleton_insert_inj_eq')

  show "\<mu>_forall D f = f3" using 3 4 by simp
qed
lemma \<open>f` D = {n3, t3, f3} \<Longrightarrow> \<mu>_forall D f = n3\<close>
  using image_iff[of "n3"] by (metis \<mu>_forall.simps insertI1)

abbreviation \<mu>:: \<open>('v, bool3) scheme\<close>
  where \<open>\<mu> \<equiv> (f3, t3, \<mu>_not, \<mu>_and, \<mu>_forall)\<close>

fun \<kappa>_not::\<open>bool3 \<Rightarrow> bool3\<close> where
\<open>\<kappa>_not t3 = f3\<close> |
\<open>\<kappa>_not f3 = t3\<close> |
\<open>\<kappa>_not n3 = n3\<close>

lemma \<kappa>_not_monot: \<open>b1 \<le> b2 \<Longrightarrow> \<kappa>_not b1 \<le> \<kappa>_not b2\<close> 
  by (smt \<kappa>_not.elims leq3.simps(2) leq3.simps(3) leq3.simps(4) leq3.simps(5) leq3.simps(6) leq3.simps(7) leq3.simps(8) leq3.simps(9) less_eq_bool3_def)

fun \<kappa>_and::\<open>bool3 \<Rightarrow> bool3 \<Rightarrow> bool3\<close> where
\<open>\<kappa>_and f3 _ = f3\<close> | \<open>\<kappa>_and _ f3 = f3\<close> |
\<open>\<kappa>_and t3 t3 = t3\<close> | \<open>\<kappa>_and t3 n3 = n3\<close> |
\<open>\<kappa>_and n3 t3 = n3\<close> | \<open>\<kappa>_and n3 n3 = n3\<close>

lemma \<kappa>_and_monot: \<open>\<lbrakk> f1 \<le> fm2 ; g1 \<le> g2 \<rbrakk> \<Longrightarrow> \<kappa>_and f1 g1 \<le> \<kappa>_and fm2 g2\<close>
  by(cases "f1"; cases "fm2"; cases "g1"; cases "g2"; simp add:less_eq_bool3_def)

(*
fun \<kappa>_forall :: \<open>bool3 set \<Rightarrow> bool3\<close> where
"\<kappa>_forall B = ( if B \<noteq> {} then ( if B = {t3}
            then t3 else (if f3 \<in> B then f3 else n3) ) else undefined)"
*)

fun \<kappa>_forall :: \<open>('v set ) \<Rightarrow> ('v \<Rightarrow> bool3) \<Rightarrow> bool3\<close> where
"\<kappa>_forall D f = ( if (\<forall> v \<in> D. f v = t3)
            then t3 else (if (\<exists> v \<in> D. f v = f3) then f3 else n3) )"

lemma \<kappa>_forall_monot:\<open>f1 \<le> fm2 \<Longrightarrow> \<kappa>_forall D f1 \<le> \<kappa>_forall D fm2\<close>
  by(cases "\<kappa>_forall D f1"; cases "\<kappa>_forall D fm2"; simp add: less_eq_bool3_def;
   metis (full_types) bool3.exhaust le_fun_def leq3.simps less_eq_bool3_def)

lemma \<open>f` D = {t3} \<Longrightarrow> \<kappa>_forall D f = t3\<close> by auto
lemma \<open>f` D = {f3} \<Longrightarrow> \<kappa>_forall D f = f3\<close> using image_iff[of "f3"] by fastforce
lemma \<open>f` D = {n3} \<Longrightarrow> \<kappa>_forall D f = n3\<close> proof-
  assume H: "f` D = {n3}"
  then have "\<exists> d \<in> D. f d = n3" using image_iff[of "n3"] by fastforce
  then have 1: "\<not>(\<forall> v \<in> D. f v = t3)" by fastforce
  from H have 2: "\<not> (\<exists> v \<in> D. f v = f3)" by force
  from 1 2 show ?thesis by simp
qed

lemma \<open>f` D = {n3, t3} \<Longrightarrow> \<kappa>_forall D f = n3\<close> proof-
  assume A: "f` D = {n3,t3}"
  from A have \<open>\<exists> v1 \<in> D. f v1 = n3\<close> using image_iff[of "n3"] by fastforce
  then obtain v1 where 1: \<open>v1 \<in> D \<and> f v1 = n3\<close> by auto
  from A have 2: "\<not>(\<exists> v\<in> D. f v = f3)" by force
  from 1 2 show ?thesis by (metis \<kappa>_forall.simps)
qed
lemma \<open>f` D = {n3, f3} \<Longrightarrow> \<kappa>_forall D f = f3\<close>
proof-
  assume "f` D = {n3, f3}"
  then have "\<exists> d \<in> D. f d = f3" using image_iff[of "f3"] by fastforce
  then show ?thesis by force
qed
lemma \<open> f` D = {f3, t3} \<Longrightarrow> \<kappa>_forall D f = f3\<close>
proof-
  assume "f` D = {f3, t3}"
  then have "\<exists> d \<in> D. f d = f3" using image_iff[of "f3"] by fastforce
  then show ?thesis by force
qed

lemma \<open>f` D = {n3, t3, f3} \<Longrightarrow> \<kappa>_forall D f = f3\<close>
proof-
  assume "f` D = {n3, t3, f3}"
  then have "\<exists> d \<in> D. f d = f3" using image_iff[of "f3"] by fastforce
  then show ?thesis by force
qed

abbreviation \<kappa>:: \<open>('v, bool3) scheme\<close>
  where \<open>\<kappa> \<equiv> (f3, t3, \<kappa>_not, \<kappa>_and, \<kappa>_forall)\<close>

fun \<nu>_not::\<open>bool4 \<Rightarrow> bool4\<close> where
"\<nu>_not t4 = f4" | "\<nu>_not f4 = t4" | "\<nu>_not n4 = n4" | "\<nu>_not b4 = b4"

fun \<nu>_and::\<open>bool4 \<Rightarrow> bool4 \<Rightarrow> bool4\<close> where
"\<nu>_and t4 (b:: bool4) = b" | "\<nu>_and (b:: bool4) t4 = b" |
"\<nu>_and f4 (b:: bool4) = f4" | "\<nu>_and (b:: bool4) f4 = f4" |
"\<nu>_and n4 n4 = n4" | "\<nu>_and b4 b4 = b4" | "\<nu>_and b4 n4 = f4"|
"\<nu>_and n4 b4 = f4"

lemma \<nu>_and_monot: \<open>\<lbrakk> f1 \<le> fm2 ; g1 \<le> g2 \<rbrakk> \<Longrightarrow> \<nu>_and f1 g1 \<le> \<nu>_and fm2 g2\<close>
  by(cases "f1"; cases "fm2"; cases "g1"; cases "g2"; simp_all add:less_eq_bool4_def)

(*
fun \<nu>_forall :: \<open>bool4 set \<Rightarrow> bool4\<close> where
"\<nu>_forall B = ( if B \<noteq> {} then ( if B = {t4}
            then t4 else (if (f4 \<in> B \<or> {n4,b4} \<subseteq> B) then f4 else(
if (B = {n4} \<or> B = {t4, n4} ) then n4 else b4
) ) ) else undefined)" *)

fun \<nu>_forall :: \<open>('v set ) \<Rightarrow> ('v \<Rightarrow> bool4) \<Rightarrow> bool4\<close> where
"\<nu>_forall D f = ( if (\<forall> v \<in> D. f v = t4) then t4
      else (if ((\<exists> v \<in> D. f v = f4) \<or> ((\<exists> v1 \<in> D. f v1 = n4) \<and> (\<exists> v2 \<in> D. f v2 = b4))) then f4
      else(if (\<forall> v \<in> D. f v = t4 \<or> f v = n4) then n4 else b4
) ) )"

fun \<nu>_forall2 :: \<open>('v set ) \<Rightarrow> ('v \<Rightarrow>bool4)\<Rightarrow> bool4\<close> where
"\<nu>_forall2 D f = ( if (f` D) = {t4}
            then t4 else (if (f4 \<in> (f` D) \<or> {n4,b4} \<subseteq> (f` D) ) then f4 else(
if ( (f` D) = {n4} \<or> (f` D) = {t4, n4} ) then n4 else b4
) ) )"

lemma \<nu>_forall\<nu>_forall2: \<open>D \<noteq> {} \<Longrightarrow> \<nu>_forall D f= \<nu>_forall2 D f\<close>
proof-
  fix D :: \<open>'v set\<close>
  fix f :: \<open>'v \<Rightarrow> bool4\<close>
  assume H: \<open>D \<noteq> {}\<close>
  show \<open>\<nu>_forall D f= \<nu>_forall2 D f\<close> proof(cases "\<forall> v\<in>D. f v= t4")
    case True
    from True have 1: "\<nu>_forall D f = t4" by simp
    from True H have "f` D = {t4}" by force
    then have 2: \<open>\<nu>_forall2 D f = t4\<close> by auto
    from 1 2 show ?thesis by auto
next
  case False
  then have F1: "\<not> (\<forall>v \<in> D. f v = t4)" by auto
  show ?thesis proof(cases "((\<exists> v \<in> D. f v = f4) \<or> ((\<exists> v1 \<in> D. f v1 = n4) \<and> (\<exists> v2 \<in> D. f v2 = b4)))")
    case True
    from True F1 have 1: "\<nu>_forall D f = f4" by simp
    from True H have "(f4 \<in> (f` D) \<or> {n4,b4} \<subseteq> (f`D) )" by force
    then have 2: \<open>\<nu>_forall2 D f = f4\<close> by auto
    from 1 2 show ?thesis by auto
  next
    case False
    then have F2: "\<not> ((\<exists> v \<in> D. f v = f4) \<or> ((\<exists> v1 \<in> D. f v1 = n4) \<and> (\<exists> v2 \<in> D. f v2 = b4)))" by auto
    then show ?thesis proof(cases "(\<forall> v\<in>D. f v = t4 \<or> f v = n4)")
      case True
      from True F1 F2 have 1: "\<nu>_forall D f = n4" by simp
      from True F1 have \<open>(\<forall> v \<in> D. f v = n4) \<or> (\<exists> v1 \<in>D . \<exists> v2 \<in> D. f v1 = t4 \<and> f v2 = n4)\<close> by blast
      then have "( ( f `D) = {n4} \<or> (f `D) = {t4, n4} )"  proof
        assume "(\<forall> v\<in>D. f v = n4)" then have "(f`D) = {n4}" using H by force
        then show ?thesis by auto
      next
        assume A: "(\<exists> v1 \<in>D. \<exists> v2\<in>D. f v1 = t4 \<and> f v2 = n4)"
        from this have \<open>( f`D) \<subseteq> {t4, n4}\<close> using True by blast
        from True have \<open>( f`D) \<supseteq> {t4, n4}\<close>
          by (metis A empty_subsetI image_eqI insert_subset)
        from \<open>( f`D) \<subseteq> {t4, n4}\<close> \<open>( f`D) \<supseteq> {t4, n4}\<close> show ?thesis by auto
      qed
    then have 2: \<open>\<nu>_forall2 D f = n4\<close> by auto
    from 1 2 show ?thesis by auto
next
  case False
  from False F1 F2 have 1: "\<nu>_forall D f = b4" by simp
  have 2: "\<nu>_forall2 D f = b4"
    by (smt F2 False \<nu>_forall2.simps imageE insertE insert_absorb insert_not_empty insert_subset image_eqI)
  from 1 2 show ?thesis by auto
qed
qed
qed
qed

fun leqL4 :: \<open>bool4 \<Rightarrow> bool4 \<Rightarrow> bool\<close> where
\<open>leqL4 _ t4 = True\<close> |
\<open>leqL4 t4 b4 = False\<close> |
\<open>leqL4 t4 n4 = False\<close> |
\<open>leqL4 t4 f4 = False\<close> |
\<open>leqL4 f4 _ = True\<close> |
\<open>leqL4 n4 f4 = False\<close> |
\<open>leqL4 b4 f4 = False\<close> |
\<open>leqL4 n4 b4 = False\<close> |
\<open>leqL4 b4 n4 = False\<close> |
\<open>leqL4 b4 b4 = True\<close> |
\<open>leqL4 n4 n4 = True\<close>

lemma leqL4_refl: "leqL4 b b = True" by(cases b) auto
lemma leqL4_antisym: " \<lbrakk> leqL4 u v ; leqL4 v u \<rbrakk> \<Longrightarrow> u = v" by(cases u; cases v) auto
lemma leqL4_trans: " \<lbrakk> leqL4 u v; leqL4 v w \<rbrakk> \<Longrightarrow> leqL4 u w" by(cases u; cases v; cases w) auto

fun leqL4inf :: \<open>bool4 \<Rightarrow> bool4 \<Rightarrow> bool4\<close> where
\<open>leqL4inf _ f4 = f4\<close> |
\<open>leqL4inf f4 _ = f4\<close> |
\<open>leqL4inf t4 (b:: bool4) = b\<close> |
\<open>leqL4inf (b:: bool4) t4 = b\<close> |
\<open>leqL4inf n4 b4 = f4\<close> |
\<open>leqL4inf b4 n4 = f4\<close> |
\<open>leqL4inf b4 b4 = b4\<close> |
\<open>leqL4inf n4 n4 = n4\<close>

text \<open>Fold with auto works better with lists than with FiniteSet.fold\<close>
fun InfL4:: \<open>bool4 list \<Rightarrow> bool4\<close> where
   "InfL4 (X :: bool4 list) = fold leqL4inf X t4"

lemma \<open> \<nu>_and b1 b2 = InfL4 [b1, b2] \<close>
  by(cases b1; cases b2; auto)

lemma H1: \<open>f `D = { b :: bool4} \<Longrightarrow> \<nu>_forall2 D f = InfL4 [b]\<close> by(cases b; auto)
lemma H2: \<open>f `D = { b1 :: bool4, b2 :: bool4 }
   \<Longrightarrow> \<nu>_forall2 D f = InfL4 [b1, b2]\<close> by(cases b1; cases b2; auto)
lemma H3: \<open>f `D = { b1 :: bool4, b2 :: bool4, b3:: bool4 }
  \<Longrightarrow> \<nu>_forall2 D f = InfL4 [b1, b2, b3]\<close>
  by(cases b1; cases b2; cases b3; auto)
lemma H4: \<open>f `D = {n4, b4, t4, f4} \<Longrightarrow> \<nu>_forall2 D f = InfL4 [n4,b4,t4,f4]\<close> by auto

lemma \<open>D \<noteq> {} \<Longrightarrow> f `D = { b :: bool4} \<Longrightarrow> \<nu>_forall D f = InfL4 [b]\<close>
  using H1 \<nu>_forall\<nu>_forall2 by metis
lemma \<open>D \<noteq> {} \<Longrightarrow> f` D = { b1 :: bool4, b2 :: bool4 }
   \<Longrightarrow> \<nu>_forall D f = InfL4 [b1, b2]\<close> using H2 \<nu>_forall\<nu>_forall2 by metis
lemma \<open>D \<noteq> {} \<Longrightarrow> f`D = { b1 :: bool4, b2 :: bool4, b3:: bool4 }
  \<Longrightarrow> \<nu>_forall D f = InfL4 [b1, b2, b3]\<close>
  using H3 \<nu>_forall\<nu>_forall2 by metis
lemma \<open>D \<noteq> {} \<Longrightarrow> f`D = {n4, b4, t4, f4} \<Longrightarrow> \<nu>_forall D f = InfL4 [n4,b4,t4,f4]\<close>
using H4 \<nu>_forall\<nu>_forall2 by metis

lemma \<nu>_not_monot: \<open>b1 \<le> b2 \<Longrightarrow> \<nu>_not b1 \<le> \<nu>_not b2\<close>
  by (smt \<nu>_not.simps bool4.exhaust leq4.elims(3) leq4.simps less_eq_bool4_def)

lemma leq4_mon: "b1 \<le> b2 \<Longrightarrow> leq4 b1 b2"
  by (simp add: less_eq_bool4_def)

lemma \<nu>_forall_monot_helper: \<open> fm1 \<le> fm2
      \<Longrightarrow> leq4 (\<nu>_forall D fm1) (\<nu>_forall D fm2)\<close>
proof-
  assume \<open>fm1 \<le> fm2\<close>
  then have H: "\<And> v. fm1 v \<le> fm2 v" using le_funD by metis
  show \<open>leq4 (\<nu>_forall D fm1) (\<nu>_forall D fm2)\<close>
  proof(cases "\<forall> v\<in>D. fm1 v= t4")
    case True
    then have T1: "\<forall> v\<in>D. fm1 v= t4" by simp
    then show ?thesis proof(cases "\<forall> v\<in>D. fm2 v= t4")
      case True
      then show ?thesis using T1 by simp
    next
      case False
      then have nT2: "\<not> (\<forall> v\<in>D. fm2 v= t4)" by auto
      then show ?thesis proof(cases "((\<exists> v \<in> D. fm2 v = f4) \<or> ((\<exists> v1 \<in> D. fm2 v1 = n4) \<and> (\<exists> v2 \<in> D. fm2 v2 = b4)))")
        case True
        then show ?thesis proof
          assume "(\<exists> v \<in> D. fm2 v = f4)"
          then obtain v where "v \<in> D" and Hv: "fm2 v = f4" by auto
          from this H have A: "fm1 v = f4 \<or> fm1 v = n4"
            by (metis bool4.exhaust leq4.simps(13) leq4.simps(7) leq4_mon)
          from T1 have B: "fm1 v = t4" using \<open>v \<in> D\<close> by simp
          from A B show ?thesis by simp
        next
          assume "(\<exists>v1\<in>D. fm2 v1 = n4) \<and> (\<exists>v2\<in>D. fm2 v2 = b4)"
           then obtain v where "v \<in> D" and Hv: "fm2 v = n4" by auto
          from this H have A: "fm1 v = n4"
            by (metis T1 leq4.simps(5) leq4_mon)
          from T1 have B: "fm1 v = t4" using \<open>v \<in> D\<close> by simp
          from A B show ?thesis by simp
        qed
      next
        case False
        then have nF2: "\<not> ((\<exists>v\<in>D. fm2 v = f4) \<or> (\<exists>v1\<in>D. fm2 v1 = n4) \<and> (\<exists>v2\<in>D. fm2 v2 = b4))" by auto
        show ?thesis proof(cases "(\<forall> v\<in>D. fm2 v = t4 \<or> fm2 v = n4)")
          case True
          from this nT2 have "\<exists> v \<in> D. fm2 v = n4" by auto
          then obtain v where \<open>v \<in> D\<close> and \<open>fm2 v = n4\<close> by auto
          from H this have A: "fm1 v = n4" by (metis T1 leq4.simps(5) leq4_mon)
          from T1 \<open>v \<in> D\<close> have B:"fm1 v = t4" by auto
          from A B show ?thesis by simp
        next
          case False
          then have "\<nu>_forall D fm2 = b4" using nF2 nT2 by simp
          then show ?thesis by simp
        qed
      qed
    qed
next
  case False
  then have nT1: "\<not> (\<forall>v\<in>D. fm1 v = t4)" by auto
  show ?thesis proof (cases  "((\<exists> v \<in> D. fm1 v = f4) \<or> ((\<exists> v1 \<in> D. fm1 v1 = n4) \<and> (\<exists> v2 \<in> D. fm1 v2 = b4)))")
    case True
    then have F1: "((\<exists> v \<in> D. fm1 v = f4) \<or> ((\<exists> v1 \<in> D. fm1 v1 = n4) \<and> (\<exists> v2 \<in> D. fm1 v2 = b4)))" by auto
    show ?thesis proof(cases "\<forall> v\<in>D. fm2 v= t4")
      case True
      then show ?thesis by (metis F1 H leq4.simps(12) leq4.simps(9) leq4_mon)
    next
      case False
      then have nT2: "\<not> (\<forall> v\<in>D. fm2 v= t4)" by auto
      then show ?thesis proof(cases "((\<exists> v \<in> D. fm2 v = f4) \<or> ((\<exists> v1 \<in> D. fm2 v1 = n4) \<and> (\<exists> v2 \<in> D. fm2 v2 = b4)))")
        case True
        then have 1: \<open>\<nu>_forall D fm2 = f4\<close> by fastforce
        from F1 have 2: \<open>\<nu>_forall D fm1 = f4\<close> by fastforce
        from 1 2 show ?thesis by simp
      next
        case False
        then have nF2: "\<not> ((\<exists>v\<in>D. fm2 v = f4) \<or> (\<exists>v1\<in>D. fm2 v1 = n4) \<and> (\<exists>v2\<in>D. fm2 v2 = b4))" by auto
        show ?thesis proof(cases "(\<forall> v\<in>D. fm2 v = t4 \<or> fm2 v = n4)")
          case True
          from this have A: "(\<forall> v\<in>D. fm1 v = t4 \<or> fm1 v = n4)" using H
            by (metis bool4.exhaust leq4.simps(11) leq4.simps(12) leq4.simps(8) leq4.simps(9) leq4_mon)
          from F1 show ?thesis using A by auto
            text \<open>Contradiction with both branches of Falsity of fm1\<close>
        next
          case False
          then have "\<nu>_forall D fm2 = b4" using nF2 nT2 by simp
          then show ?thesis by simp
        qed
      qed
    qed
  next
    case False
    then have nF1: "\<not> ((\<exists> v \<in> D. fm1 v = f4) \<or> ((\<exists> v1 \<in> D. fm1 v1 = n4) \<and> (\<exists> v2 \<in> D. fm1 v2 = b4)))" by auto
    then show ?thesis proof(cases "(\<forall> v \<in> D. fm1 v = t4 \<or> fm1 v = n4)")
        case True
        then have "\<nu>_forall D fm1 = n4" using nF1 nT1 by simp
        then show ?thesis by simp
      next
        case False
        then have nN1: "\<not> (\<forall> v \<in> D. fm1 v = t4 \<or> fm1 v = n4)" by auto
        show ?thesis proof(cases "\<forall> v\<in>D. fm2 v= t4")
          case True
          from this H have "\<forall> v \<in>D. fm1 v \<le> t4" by metis
          hence "\<forall> v \<in> D. fm1 v = n4 \<or> fm1 v = t4"
            by (metis bool4.exhaust leq4.simps(12) leq4_mon nF1)
          then show ?thesis using nT1 nF1 by auto text \<open>Some contradiction.... \<close>
    next
      case False
      then have nT2: "\<not> (\<forall> v\<in>D. fm2 v= t4)" by auto
      then show ?thesis proof(cases "((\<exists> v \<in> D. fm2 v = f4) \<or> ((\<exists> v1 \<in> D. fm2 v1 = n4) \<and> (\<exists> v2 \<in> D. fm2 v2 = b4)))")
        case True
        then show ?thesis proof
          assume "\<exists>v\<in>D. fm2 v = f4"
          then obtain v where \<open>v \<in> D\<close> and \<open>fm2 v = f4\<close> by auto
          from this H have A: "fm1 v = f4 \<or> fm1 v = n4"
            by (metis bool4.exhaust leq4.simps(13) leq4.simps(7) leq4_mon)
          from nF1 have Res1: "(\<forall>v\<in>D. fm1 v \<noteq> f4)" by simp
          from this A \<open>v \<in> D\<close> have B: "fm1 v = n4" by auto
          from nF1 have "((\<forall> v1 \<in> D. fm1 v1 \<noteq> n4) \<or> (\<forall> v2 \<in> D. fm1 v2 \<noteq> b4))" by simp
          from this B \<open>v \<in> D\<close> have Res2: "(\<forall> v \<in> D. fm1 v \<noteq> b4)" by auto
          from Res1 Res2 show ?thesis using nN1 \<open>v \<in> D\<close>
            using bool4.exhaust by blast
        next
          assume As: "(\<exists>v1\<in>D. fm2 v1 = n4) \<and> (\<exists>v2\<in>D. fm2 v2 = b4)"
          from As obtain v1 where \<open>v1 \<in> D\<close> and "fm2 v1 = n4" by auto
          from this H have B: "fm1 v1 = n4"
            by (metis bool4.exhaust leq4.simps(11) leq4.simps(5) leq4.simps(8) leq4_mon)
          from nF1 have Res1: "(\<forall>v\<in>D. fm1 v \<noteq> f4)" by simp
          from nF1 have "((\<forall> v1 \<in> D. fm1 v1 \<noteq> n4) \<or> (\<forall> v2 \<in> D. fm1 v2 \<noteq> b4))" by simp
          from this B \<open>v1 \<in> D\<close> have Res2: "(\<forall> v \<in> D. fm1 v \<noteq> b4)" by auto
          from Res1 Res2 show ?thesis using nN1 \<open>v1 \<in> D\<close>
            using bool4.exhaust by blast
        qed
      next
        case False
        then have nF2: "\<not> ((\<exists>v\<in>D. fm2 v = f4) \<or> (\<exists>v1\<in>D. fm2 v1 = n4) \<and> (\<exists>v2\<in>D. fm2 v2 = b4))" by auto
        show ?thesis proof(cases "(\<forall> v\<in>D. fm2 v = t4 \<or> fm2 v = n4)")
          case True
          from this have A: "(\<forall> v\<in>D. fm1 v = t4 \<or> fm1 v = n4)" using H
            by (metis bool4.exhaust leq4.simps(11) leq4.simps(12) leq4.simps(8) leq4.simps(9) leq4_mon)
          from nT1 nN1 show ?thesis using A by auto text \<open>Contradiction with both branches of Falsity of fm1\<close>
        next
          case False
          then have "\<nu>_forall D fm2 = b4" using nF2 nT2 by simp
          then show ?thesis by simp
        qed
      qed
    qed
   qed
  qed
qed
qed

(* Old proof (somewhat shorter ... but only works for D= UNIV hardcoded.... :(
apply(cases "\<nu>_forall D f1"; cases "\<nu>_forall D fm2"; simp)
 metis (full_types) bool4.distinct bool4.exhaust leq4.elims(2) leq4.simps(5))
 *)

lemma \<nu>_forall_monot: \<open>f1 \<le> fm2
      \<Longrightarrow> (\<nu>_forall D f1) \<le> (\<nu>_forall D fm2)\<close>
proof-
  assume \<open>f1 \<le> fm2\<close>
(*  then have "\<forall> v. f1 v \<le> fm2 v" by (simp add: le_funD)
  then have "\<forall> v. leq4 (f1 v) (fm2 v)" using less_eq_bool4_def by simp *)
  then have "leq4 (\<nu>_forall D f1) (\<nu>_forall D fm2)" by(metis \<nu>_forall_monot_helper)
  then show "(\<nu>_forall D f1) \<le> (\<nu>_forall D fm2)" using less_eq_bool4_def by simp
qed

abbreviation \<nu>:: \<open>('v, bool4) scheme\<close>
  where \<open>\<nu> \<equiv> (f4, t4, \<nu>_not, \<nu>_and, \<nu>_forall)\<close>

fun value_fm_\<tau> :: \<open>'v assignment \<Rightarrow> ('v, 'a, 'b, 'c, bool2) model \<Rightarrow> ('a, 'b, 'c) fm \<Rightarrow> bool2\<close> where
\<open>value_fm_\<tau> w (D, Cw, Fw, Rw) f = value_fm \<tau> w (D, Cw, Fw, Rw) f\<close>

fun value_fm_\<kappa> :: \<open>'v assignment \<Rightarrow> ('v, 'a, 'b, 'c, bool3) model \<Rightarrow> ('a, 'b, 'c) fm \<Rightarrow> bool3\<close> where
\<open>value_fm_\<kappa> w (D, Cw, Fw, Rw) f = value_fm \<kappa> w (D, Cw, Fw, Rw) f\<close>

fun value_fm_\<mu> :: \<open>'v assignment \<Rightarrow> ('v, 'a, 'b, 'c, bool3) model \<Rightarrow> ('a, 'b, 'c) fm \<Rightarrow> bool3\<close> where
\<open>value_fm_\<mu> w (D, Cw, Fw, Rw) f = value_fm \<mu> w (D, Cw, Fw, Rw) f\<close>

fun value_fm_\<nu> :: \<open>'v assignment \<Rightarrow> ('v, 'a, 'b, 'c, bool4) model \<Rightarrow> ('a, 'b, 'c) fm \<Rightarrow> bool4\<close> where
\<open>value_fm_\<nu> w (D, Cw, Fw, Rw) f = value_fm \<nu> w (D, Cw, Fw, Rw) f\<close>

fun lift23 :: \<open>bool2 \<Rightarrow> bool3\<close> where
"lift23 t2 = t3" |"lift23 f2 = f3"

fun lift24 :: \<open>bool2 \<Rightarrow> bool4\<close> where
"lift24 t2 = t4" |"lift24 f2 = f4"

lemma \<kappa>_and_lift_commute:
\<open>lift23 ( \<tau>_and A B) = \<kappa>_and (lift23 A) (lift23 B)\<close>
  by(cases A; cases B; auto)

lemma \<kappa>_not_lift_commute:
\<open>lift23 (\<tau>_not A) = \<kappa>_not (lift23 A)\<close>
  by(cases A; auto)

lemma \<kappa>_forall_lift_commute:
   \<open>lift23 (\<tau>_forall D f) = \<kappa>_forall D (\<lambda> v. lift23 (f v))\<close>
proof(cases "\<forall> v. f v = t2")
  case True
  then show ?thesis using lift23.elims by auto
next
  case False
  then show ?thesis using lift23.elims by auto
qed

lemma \<mu>_and_lift_commute:
\<open>lift23 ( \<tau>_and A B) = \<mu>_and (lift23 A) (lift23 B)\<close>
  by(cases A; cases B; auto)

lemma \<mu>_not_lift_commute:
\<open>lift23 (\<tau>_not A) = \<mu>_not (lift23 A)\<close>
  by(cases A; auto)

lemma \<mu>_forall_lift_commute:
   \<open>lift23 (\<tau>_forall D f) = \<mu>_forall D (\<lambda> v. lift23 (f v))\<close>
proof(cases "\<forall> v. f v = t2")
  case True
  then show ?thesis using lift23.elims by simp
next
  case False
  then show ?thesis using lift23.elims by auto
qed

lemma \<nu>_and_lift_commute:
\<open>lift24 ( \<tau>_and A B) = \<nu>_and (lift24 A) (lift24 B)\<close>
  by(cases A; cases B; auto)

lemma \<nu>_not_lift_commute :
\<open>lift24 (\<tau>_not A) = \<nu>_not (lift24 A)\<close>
  by(cases A; auto)

lemma \<nu>_forall_lift_commute:
   \<open>lift24 (\<tau>_forall D f) = \<nu>_forall D (\<lambda> v. lift24 (f v))\<close>
proof(cases "\<forall> v. f v= t2")
  case True
  then show ?thesis using lift24.elims by auto
next
  case False
  then show ?thesis using lift24.elims by auto
qed

lemma \<kappa>_lift_Rel_commute:
"value_fm_\<kappa> w (D, Cw, Fw, \<lambda>symb fmlist. lift23 (Rw symb fmlist)) f 
  =lift23 (value_fm_\<tau> w (D, Cw, Fw, Rw) f)"
proof(induction f arbitrary: w)
case (Rel x1 x2)
  then show ?case by simp
next
  case (Equ x1 x2)
  then show ?case by simp
next
  case Fal
  then show ?case by simp
next
  case (And fm1 fm2)
  then show ?case using \<kappa>_and_lift_commute by simp
next
  case (Neg f)
  then show ?case using \<kappa>_not_lift_commute by simp
next
  case (Forall m f)
  then have IH: "\<And> w. value_fm_\<kappa> w (D, Cw, Fw, \<lambda>rsymb flist. lift23 (Rw rsymb flist))
   f = lift23 (value_fm_\<tau> w (D, Cw, Fw, Rw) f)" by(simp)
  let ?f = "(\<lambda>v. value_fm_\<tau> (\<lambda>k. if k = m then v else w k) (D, Cw, Fw, Rw) f)"
  have "(value_fm_\<tau> w (D, Cw, Fw, Rw) (Forall m f)) = \<tau>_forall D ?f" by auto
  from this have A: "lift23 ( value_fm_\<tau> w (D, Cw, Fw, Rw)
     (Forall m f)) = \<kappa>_forall D (\<lambda> v. lift23 (?f v))" using \<kappa>_forall_lift_commute by(rule HOL.ssubst)
  from this IH show ?case by(cases "(value_fm_\<tau> w (D, Cw, Fw, Rw) (Forall m f))"; simp)
qed

lemma \<mu>_lift_Rel_commute:
"value_fm_\<mu> w (D, Cw, Fw, \<lambda>symb fmlist. lift23 (Rw symb fmlist)) f 
  =lift23 (value_fm_\<tau> w (D, Cw, Fw, Rw) f)"
proof(induction f arbitrary: w)
case (Rel x1 x2)
  then show ?case by simp
next
  case (Equ x1 x2)
  then show ?case by simp
next
  case Fal
  then show ?case by simp
next
  case (And fm1 fm2)
  then show ?case using \<mu>_and_lift_commute by simp
next
  case (Neg f)
  then show ?case using \<mu>_not_lift_commute by simp
next
  case (Forall m f)
  then have IH: "\<And> w. value_fm_\<mu> w (D, Cw, Fw, \<lambda>rsymb flist. lift23 (Rw rsymb flist))
   f = lift23 (value_fm_\<tau> w (D, Cw, Fw, Rw) f)" by auto
  let ?f = "(\<lambda>v. value_fm_\<tau> (\<lambda>k. if k = m then v else w k) (D, Cw, Fw, Rw) f)"
  have "(value_fm_\<tau> w (D, Cw, Fw, Rw) (Forall m f)) = \<tau>_forall D ?f" by auto
  from this have A: "lift23 ( value_fm_\<tau> w (D, Cw, Fw, Rw)
     (Forall m f)) = \<mu>_forall D (\<lambda> v. lift23 (?f v))" using \<mu>_forall_lift_commute by(rule HOL.ssubst)
  from this IH show ?case by(cases "(value_fm_\<tau> w (D, Cw, Fw, Rw) (Forall m f))") simp_all
qed

lemma \<nu>_lift_Rel_commute:
"value_fm_\<nu> w (D, Cw, Fw, \<lambda>symb fmlist. lift24 (Rw symb fmlist)) f 
  =lift24 (value_fm_\<tau> w (D, Cw, Fw, Rw) f)"
proof(induction f arbitrary: w)
case (Rel x1 x2)
  then show ?case by simp
next
  case (Equ x1 x2)
  then show ?case by simp
next
  case Fal
  then show ?case by simp
next
  case (And fm1 fm2)
  then show ?case using \<nu>_and_lift_commute by simp
next
  case (Neg f)
  then show ?case using \<nu>_not_lift_commute by simp
next
  case (Forall m f)
  then have IH: "\<And> w. value_fm_\<nu> w (D, Cw, Fw, \<lambda>rsymb flist. lift24 (Rw rsymb flist))
   f = lift24 (value_fm_\<tau> w (D, Cw, Fw, Rw) f)" by auto
  let ?f = "(\<lambda>v. value_fm_\<tau> (\<lambda>k. if k = m then v else w k) (D, Cw, Fw, Rw) f)"
  have "(value_fm_\<tau> w (D, Cw, Fw, Rw) (Forall m f)) = \<tau>_forall D ?f" by auto
  from this have A: "lift24 ( value_fm_\<tau> w (D, Cw, Fw, Rw)
     (Forall m f)) = \<nu>_forall D (\<lambda> v. lift24 (?f v))" using \<nu>_forall_lift_commute by(rule HOL.ssubst)
  from this IH show ?case by(cases "(value_fm_\<tau> w (D, Cw, Fw, Rw) (Forall m f))") simp_all
qed

lemma tau_\<kappa>_coinc:
"lift23 (value_fm_\<tau> w (D, Cw, Fw, Rw) (f :: ('a, 'b, 'c) fm))
  = (value_fm_\<kappa> w (D, Cw, Fw, (\<lambda> rsymb. \<lambda> flist. lift23 (Rw rsymb flist)) ) f)"
proof(induction f)
case (Rel x1 x2)
  then show ?case by simp
next
  case (Equ x1 x2)
then show ?case by simp
next
  case Fal
  then show ?case by simp
next
  case (And fm1 fm2)
  then show ?case using \<kappa>_and_lift_commute by simp
next
  case (Neg f)
  then show ?case using \<kappa>_not_lift_commute by simp
next
  case (Forall m f)
  then show ?case using \<kappa>_lift_Rel_commute by metis
qed

lemma tau_\<mu>_coinc:
"lift23 (value_fm_\<tau> w (D, Cw, Fw, Rw) (f :: ('a, 'b, 'c) fm))
  = (value_fm_\<mu> w (D, Cw, Fw, (\<lambda> rsymb. \<lambda> flist. lift23 (Rw rsymb flist)) ) f)"
proof(induction f)
case (Rel x1 x2)
  then show ?case by simp
next
  case (Equ x1 x2)
then show ?case by simp
next
  case Fal
  then show ?case by simp
next
  case (And fm1 fm2)
  then show ?case using \<mu>_and_lift_commute by simp
next
  case (Neg f)
  then show ?case using \<mu>_not_lift_commute by simp
next
  case (Forall m f)
  then show ?case using \<mu>_lift_Rel_commute by metis
qed

lemma tau_\<nu>_coinc:
"lift24 (value_fm_\<tau> w (D, Cw, Fw, Rw) (f :: ('a, 'b, 'c) fm))
  = (value_fm_\<nu> w (D, Cw, Fw, (\<lambda> rsymb. \<lambda> flist. lift24 (Rw rsymb flist)) ) f)"
proof(induction f)
case (Rel x1 x2)
  then show ?case by simp
next
  case (Equ x1 x2)
then show ?case by simp
next
  case Fal
  then show ?case by simp
next
  case (And fm1 fm2)
  then show ?case using \<nu>_and_lift_commute by simp
next
  case (Neg f)
  then show ?case using \<nu>_not_lift_commute by simp
next
  case (Forall m f)
  then show ?case using \<nu>_lift_Rel_commute by metis
qed

lemma monot_\<mu>_\<kappa>_leq3: "(\<forall> v. leq3 ((fm1 :: 'v \<Rightarrow> bool3) v) ((fm2 :: 'v \<Rightarrow> bool3) v))
        \<Longrightarrow> leq3 (\<mu>_forall D fm1) (\<kappa>_forall D fm2)"
  apply(cases "\<mu>_forall D fm1") apply(cases "\<kappa>_forall D fm2") apply(simp_all)
  apply (metis (full_types) bool3.exhaust leq3.simps(6) leq3.simps(7) less_eq_bool3_def)
  by(metis (full_types) bool3.exhaust leq3.simps(2) leq3.simps(3) leq3.simps(8) leq3.simps(9) less_eq_bool3_def)

lemma monot_\<mu>_\<kappa>: "(fm1 :: 'v \<Rightarrow> bool3) \<le> (fm2 :: 'v \<Rightarrow> bool3)
        \<Longrightarrow> (\<mu>_forall D fm1) \<le> (\<kappa>_forall D fm2)"
proof-
  assume "fm1 \<le> fm2"
  from this le_fun_def[of "fm1" "fm2"] have "(\<forall>v. fm1 v \<le> fm2 v)" by simp
  from this less_eq_bool3_def have "\<forall>v. leq3 (fm1 v) (fm2 v)" by simp
  from this monot_\<mu>_\<kappa>_leq3[of "fm1" "fm2"] have "leq3 (\<mu>_forall D fm1)
     (\<kappa>_forall D fm2)" by simp
  from this less_eq_bool3_def show "(\<mu>_forall D fm1) \<le> (\<kappa>_forall D fm2)" by simp
qed

lemma \<kappa>_\<mu>_leq_prop:
   \<open>(\<And> w. (value_fm_\<mu> w (D, Cw, Rw, Fw) f) \<le> (value_fm_\<kappa> w (D, Cw, Rw, Fw) f))
   \<Longrightarrow> (value_fm_\<mu> w (D, Cw, Rw, Fw) (Forall m f) ) \<le> (value_fm_\<kappa> w (D, Cw, Rw, Fw) (Forall m f) )\<close>
proof-
  assume H: "\<And> w. (value_fm_\<mu> w (D, Cw, Rw, Fw) f) \<le> (value_fm_\<kappa> w (D, Cw, Rw, Fw) f)"
  let ?f2 = " \<lambda> v. value_fm_\<kappa> (\<lambda> k. if k=m then v else w k) (D, Cw,Rw,Fw) f"
  let ?f1 = " \<lambda> v. value_fm_\<mu> (\<lambda> k. if k=m then v else w k) (D, Cw,Rw,Fw) f"
  have 1: "value_fm_\<mu> w (D, Cw, Rw, Fw) (Forall m f) = \<mu>_forall D ?f1" by simp
  have 2: "value_fm_\<kappa> w (D, Cw, Rw, Fw) (Forall m f) = \<kappa>_forall D ?f2" by simp
  from H have "?f1 \<le> ?f2 " by (simp add: le_funI less_eq_bool3_def)
  from this have " \<mu>_forall D ?f1 \<le> \<kappa>_forall D ?f2" using less_eq_bool3_def monot_\<mu>_\<kappa> by blast
  then show "(value_fm_\<mu> w (D, Cw, Rw, Fw) (Forall m f)) \<le> ( value_fm_\<kappa> w (D, Cw, Rw, Fw) (Forall m f))"
    using 1 2 by simp 
qed

lemma val\<mu>leq\<kappa>:
"(value_fm_\<mu> w (D, Cw, Fw, Rw) f) \<le> (value_fm_\<kappa> w (D, Cw, Fw, Rw ) f)"
proof(induction f arbitrary: w)
case (Rel x1 x2)
  then show ?case
    by(cases "(value_fm_\<mu> w (D, Cw, Fw, Rw) (Rel x1 x2))") simp_all
next
  case (Equ x1 x2)
  then show ?case by simp
next
  case Fal
  then show ?case by simp
next
  case (And fm1 fm2)
  then have H1: "\<And> w. (value_fm_\<mu> w (D, Cw, Fw, Rw) fm1) \<le> (value_fm_\<kappa> w (D, Cw, Fw, Rw) fm1)"
   and H2: "\<And> w. (value_fm_\<mu> w (D, Cw, Fw, Rw) fm2) \<le> (value_fm_\<kappa> w (D, Cw, Fw, Rw) fm2)" by auto
  fix w
  from H1[of "w"] H2[of "w"] show "(value_fm_\<mu> w (D, Cw, Fw, Rw) (And fm1 fm2)) \<le>
              (value_fm_\<kappa> w (D, Cw, Fw, Rw) (And fm1 fm2))"
    by(cases "value_fm_\<mu> w (D, Cw, Fw, Rw) fm1";
   cases "value_fm_\<mu> w (D, Cw, Fw, Rw) fm2";
   cases "value_fm_\<kappa> w (D, Cw, Fw, Rw) fm1";
   cases "value_fm_\<kappa> w (D, Cw, Fw, Rw) fm2") (simp_all add: less_eq_bool3_def)
next
  case (Neg f)
  then have H: "\<And> w. (value_fm_\<mu> w (D, Cw, Fw, Rw) f) \<le>
                        (value_fm_\<kappa> w (D, Cw, Fw, Rw) f)" by auto
  fix w
  from H[of "w"] show "(value_fm_\<mu> w (D, Cw, Fw, Rw) (Neg f)) \<le>
          (value_fm_\<kappa> w (D, Cw, Fw, Rw) (Neg f))"
     by(cases "(value_fm_\<mu> w (D, Cw, Fw, Rw) f)";
        cases "(value_fm_\<kappa> w (D, Cw, Fw, Rw) f)")
          (simp_all add: less_eq_bool3_def)
next
  case (Forall m f)
  then show ?case by(rule \<kappa>_\<mu>_leq_prop)
qed

(*
type_synonym ('v, 'a,'b,'c, 'mybool) modelwS
   = \<open>'v set \<times> ('v, 'a,'b,'c) const_mod \<times> ('v, 'a,'b,'c) func_mod \<times> ('v, 'a,'b,'c, 'mybool) rela_mod\<close>
*)

fun leqMod ::\<open>('v, 'a,'b,'c, ('mybool::order) ) model \<Rightarrow> ('v, 'a,'b,'c, 'mybool) model \<Rightarrow> bool\<close>
  where "leqMod (Da, Cwa, Fwa, Rwa) (Db, Cwb, Fwb, Rwb) = ( (Da = Db) \<and> Cwa = Cwb \<and> Fwa = Fwb \<and> Rwa \<le> Rwb)"

lemma leqMod_refl: "leqMod M M = True"
  by (metis (no_types, lifting) leqMod.simps order_refl prod_cases4)
lemma leqMod_antisym: " \<lbrakk> leqMod M1 M2 ; leqMod M2 M1 \<rbrakk> \<Longrightarrow> M1 = M2"
  by (smt order_antisym leqMod.elims(2) leqMod.simps)
lemma leqMod_trans: " \<lbrakk> leqMod M1 M2; leqMod M2 M3 \<rbrakk> \<Longrightarrow> leqMod M1 M3"
  by (smt order.trans leqMod.elims(2) leqMod.simps)

(*
fun leqModUNIV ::\<open>('v, 'a,'b,'c, ('mybool::order) ) model \<Rightarrow> ('v, 'a,'b,'c, 'mybool) model \<Rightarrow> bool\<close>
  where "leqModUNIV (Da, Cwa, Fwa, Rwa) (Db, Cwb, Fwb, Rwb) =
    ( Da = UNIV \<and> Db = UNIV \<and> Cwa = Cwb \<and> Fwa = Fwb \<and> (Rwa \<le> Rwb))"

lemma leqModUNIV_refl: "leqModUNIV M M = True"
  using leqModUNIV.elims(3) by blast
lemma leqModUNIV_antisym: " \<lbrakk> leqModUNIV M1 M2 ; leqModUNIV M2 M1 \<rbrakk> \<Longrightarrow> M1 = M2"
  by (smt Pair_inject order_antisym leqModUNIV.elims(2))
lemma leqModUNIV_trans: " \<lbrakk> leqModUNIV M1 M2; leqModUNIV M2 M3 \<rbrakk> \<Longrightarrow> leqModUNIV M1 M3"
  by (smt dual_order.trans leqModUNIV.elims(2) leqModUNIV.simps)
*)

lemma monot_in_\<tau>: \<open>( DA = DB \<and> CwA = CwB \<and> FwA = FwB \<and> (\<forall> rsym fmlist. leq2 (RwA rsym fmlist) (RwB rsym fmlist)))
    \<Longrightarrow> leq2 (value_fm_\<tau> s (DA, CwA, FwA, RwA) f) (value_fm_\<tau> s (DB, CwB, FwB, RwB) f)\<close>
proof(induction f arbitrary: s)
case (Rel x1 x2)
  then show ?case by auto
next
  case (Equ x1 x2)
  then show ?case by simp
next
  case Fal
  then show ?case by simp
next
  case (And f1 f2)
  then show ?case using \<tau>_and_monot by(simp add: less_eq_bool2_def)
next
  case (Neg f)
  then show ?case using \<tau>_not_monot by(simp add: less_eq_bool2_def)
next
  case (Forall m f)
  then have IH: "\<forall> s. value_fm_\<tau> s (DA, CwA, FwA, RwA) f 
                   \<le> value_fm_\<tau> s (DB, CwB, FwB, RwB) f" by(simp add: less_eq_bool2_def)
  fix s
  let ?fA = "\<lambda> v. value_fm_\<tau> (\<lambda> k. if k=m then v else s k) (DA, CwA,FwA,RwA) f"
  let ?fB = "\<lambda> v. value_fm_\<tau> (\<lambda> k. if k=m then v else s k) (DB, CwB,FwB,RwB) f"

  from IH have "\<forall> v. ?fA v \<le> ?fB v" by simp then have \<open>?fA \<le> ?fB\<close> by (simp add: le_funI)
  from this \<tau>_forall_monot Forall have "\<tau>_forall DA ?fA \<le> \<tau>_forall DB ?fB" by blast

  then show "leq2 (value_fm_\<tau> s (DA, CwA, FwA, RwA) (Forall m f))
        ( value_fm_\<tau> s (DB, CwB, FwB, RwB) (Forall m f) )" by(simp add: less_eq_bool2_def)
qed

lemma monot_in_\<kappa>: \<open>leqMod (DA, CwA, FwA, RwA) (DB, CwB, FwB, RwB)
    \<Longrightarrow> value_fm_\<kappa> s (DA, CwA, FwA, RwA) f \<le> value_fm_\<kappa> s (DB, CwB, FwB, RwB) f\<close>
proof(induction f arbitrary: s)
case (Rel x1 x2)
then show ?case by (simp add: le_funD)
next
  case (Equ x1 x2)
  then show ?case by simp
next
case Fal
  then show ?case by simp
next
  case (And f1 f2)
  then show ?case using \<kappa>_and_monot by simp
next
  case (Neg f)
  then show ?case using \<kappa>_not_monot by simp
next
  case (Forall m f)
  then have IH: "\<forall> s. value_fm_\<kappa> s (DA, CwA, FwA, RwA) f 
                   \<le> value_fm_\<kappa> s (DB, CwB, FwB, RwB) f" by auto
  fix s
  let ?fA = "\<lambda> v. value_fm_\<kappa> (\<lambda> k. if k=m then v else s k) (DA, CwA,FwA,RwA) f"
  let ?fB = "\<lambda> v. value_fm_\<kappa> (\<lambda> k. if k=m then v else s k) (DB, CwB,FwB,RwB) f"

  from Forall have \<open>DA = DB\<close> by auto
  from IH have "\<forall> v. ?fA v \<le> ?fB v" by simp then have \<open>?fA \<le> ?fB\<close> by (simp add: le_funI)
  from this \<kappa>_forall_monot have "\<kappa>_forall DA ?fA \<le> \<kappa>_forall DB ?fB"
    using \<open>DA = DB\<close> by blast

  then show "value_fm_\<kappa> s (DA, CwA, FwA, RwA) (Forall m f)
        \<le> value_fm_\<kappa> s (DB, CwB, FwB, RwB) (Forall m f)" by simp
qed

lemma monot_in_\<mu>: \<open>leqMod (DA, CwA, FwA, RwA) (DB, CwB, FwB, RwB)
    \<Longrightarrow> value_fm_\<mu> s (DA, CwA, FwA, RwA) f \<le> value_fm_\<mu> s (DB, CwB, FwB, RwB) f\<close>
proof(induction f arbitrary: s)
case (Rel x1 x2)
then show ?case by (simp add: le_funD)
next
  case (Equ x1 x2)
  then show ?case by simp
next
case Fal
  then show ?case by simp
next
  case (And f1 f2)
  then show ?case using \<mu>_and_monot by simp
next
  case (Neg f)
  then show ?case using \<mu>_not_monot by simp
next
  case (Forall m f)
  then have IH: "\<forall> s. value_fm_\<mu> s (DA, CwA, FwA, RwA) f 
                   \<le> value_fm_\<mu> s (DB, CwB, FwB, RwB) f" by auto
  fix s
  let ?fA = "\<lambda> v. value_fm_\<mu> (\<lambda> k. if k=m then v else s k) (DA, CwA,FwA,RwA) f"
  let ?fB = "\<lambda> v. value_fm_\<mu> (\<lambda> k. if k=m then v else s k) (DB, CwB,FwB,RwB) f"

  from Forall have \<open>DA = DB\<close> by auto
  from IH have "\<forall> v. ?fA v \<le> ?fB v" by simp then have \<open>?fA \<le> ?fB\<close> by (simp add: le_funI)
  from this \<mu>_forall_monot \<open>DA = DB\<close> have "\<mu>_forall DA ?fA \<le> \<mu>_forall DB ?fB" by blast

  then show "value_fm_\<mu> s (DA, CwA, FwA, RwA) (Forall m f)
        \<le> value_fm_\<mu> s (DB, CwB, FwB, RwB) (Forall m f)" by simp
qed

lemma monot_in_\<nu>: \<open>leqMod (DA, CwA, FwA, RwA) (DB, CwB, FwB, RwB)
    \<Longrightarrow> value_fm_\<nu> s (DA, CwA, FwA, RwA) f \<le> value_fm_\<nu> s (DB, CwB, FwB, RwB) f\<close>
proof(induction f arbitrary: s)
case (Rel x1 x2)
then show ?case by (simp add: le_funD)
next
  case (Equ x1 x2)
  then show ?case by simp
next
case Fal
  then show ?case by simp
next
  case (And f1 f2)
  then show ?case using \<nu>_and_monot by simp
next
  case (Neg f)
  then show ?case using \<nu>_not_monot by simp
next
  case (Forall m f)
  then have IH: "\<forall> s. value_fm_\<nu> s (DA, CwA, FwA, RwA) f 
                   \<le> value_fm_\<nu> s (DB, CwB, FwB, RwB) f" by auto
  fix s
  let ?fA = "\<lambda> v. value_fm_\<nu> (\<lambda> k. if k=m then v else s k) (DA, CwA,FwA,RwA) f"
  let ?fB = "\<lambda> v. value_fm_\<nu> (\<lambda> k. if k=m then v else s k) (DB, CwB,FwB,RwB) f"

  from Forall have \<open>DA = DB\<close> by auto
  from IH have "\<forall> v. ?fA v \<le> ?fB v" by simp then have \<open>?fA \<le> ?fB\<close> by (simp add: le_funI)
  from this \<nu>_forall_monot[of "?fA" "?fB"]
    \<open>DA = DB\<close> have "\<nu>_forall DA ?fA \<le> \<nu>_forall DB ?fB" by simp

  then show "value_fm_\<nu> s (DA, CwA, FwA, RwA) (Forall m f)
        \<le> value_fm_\<nu> s (DB, CwB, FwB, RwB) (Forall m f)" by simp
qed

lemma value_fm_locdet: \<open> \<lbrakk> \<forall>m \<in> freevar f. s1 m = s2 m \<rbrakk> \<Longrightarrow>
      value_fm (myFalse, myTrue, myNot, myAnd, myUni) s1 (D, Cw, Fw, Rw) f =
       value_fm (myFalse, myTrue, myNot, myAnd, myUni) s2 (D, Cw, Fw, Rw) f\<close>
proof(induction f arbitrary: s1 s2)
  case (Rel symb tmlist)
  assume "\<forall>m\<in>freevar (Rel symb tmlist). s1 m = s2 m"
  let ?tmset = "set tmlist"
  have "freevar (Rel symb tmlist) = \<Union> ( freevar_tm` ?tmset)" by simp
  then have "\<forall> t \<in> ?tmset. freevar_tm t \<subseteq> freevar (Rel symb tmlist)" by auto
  then have "\<forall> t \<in> ?tmset. value_tm s1 (Cw, Fw) t = value_tm s2 (Cw, Fw) t "
    using value_tm_locdet using Rel.prems by blast
  then show ?case
    by (smt map_eq_conv value_fm.simps(2))
next
  case (Equ x1 x2)
  then show ?case
    by (smt UnCI freevar.simps(2) value_fm.simps(3) value_tm_locdet)
next
  case Fal
  then show ?case using value_fm.simps(1) by simp
next
  case (And f1 f2)
  then show ?case
    by (smt UnCI freevar.simps(3) value_fm.simps(4) value_fm_\<tau>.simps)
next
  case (Neg f)
  then show ?case by force
next
  case (Forall m f)
  then have "\<forall>m' \<in>freevar (Forall m f). s1 m' = s2 m'" by auto
  then have H2: "\<forall>m' \<in> freevar f. m' \<noteq> m \<longrightarrow> s1 m' = s2 m'" 
    using freevar.simps(6) by simp
  let ?S = "(myFalse, myTrue, myNot, myAnd, myUni)"

  have R: \<open>\<forall> v. value_fm ?S (\<lambda> k. if k=m then v else s1 k) (D, Cw,Fw,Rw) f 
           = value_fm ?S (\<lambda> k. if k=m then v else s2 k) (D, Cw,Fw,Rw) f\<close>
  proof
    fix v let ?s1 = "(\<lambda> k. if k=m then v else s1 k)" let ?s2 = "(\<lambda> k. if k=m then v else s2 k)"
    have "(\<forall>m\<in>freevar f. ?s1 m = ?s2 m)" using H2 by simp
    from this have "value_fm ?S ?s1 (D, Cw, Fw, Rw) f = value_fm ?S ?s2 (D, Cw, Fw, Rw) f" by(simp add: Forall.IH)
    then show \<open>value_fm ?S (\<lambda> k. if k=m then v else s1 k) (D, Cw,Fw,Rw) f = value_fm ?S (\<lambda> k. if k=m then v else s2 k) (D, Cw,Fw,Rw) f\<close> by auto
  qed

  from R show "value_fm ?S s1 (D, Cw, Fw, Rw) (Forall m f) = 
           value_fm ?S s2 (D, Cw, Fw, Rw) (Forall m f)" by simp
qed

lemma value_fm_locdetS: \<open> \<lbrakk> \<forall>m \<in> freevar f. s1 m = s2 m \<rbrakk> \<Longrightarrow>
      value_fm S s1 (D, Cw, Fw, Rw) f = value_fm S s2 (D, Cw, Fw, Rw) f\<close>
  using value_fm_locdet by (smt prod_cases5)

fun nthelement_in_set ::\<open>nat set \<Rightarrow> nat \<Rightarrow> nat\<close> where
"nthelement_in_set S 0 = Min S" |
"nthelement_in_set S (Suc n) = Min { s \<in> S . (nthelement_in_set S n) < s }"

(* Trying out this function
value "nthelement_in_set {5,35,11,3,8,15} 2" *)

(*
fun pos_in_sorted_set::\<open>nat set \<Rightarrow> nat \<Rightarrow> nat\<close> where
"pos_in_sorted_set S v = ( Eps (\<lambda> n. v = nthelement_in_set S n) )"
*)

lemma value_fm_locdetS_cont: \<open> \<lbrakk> \<forall>m \<in> contvar f. s1 m = s2 m \<rbrakk> \<Longrightarrow>
      value_fm S s1 (D, Cw, Fw, Rw) f = value_fm S s2 (D, Cw, Fw, Rw) f\<close>
  using value_fm_locdetS freevar_contvar by blast

fun pos_in_list::\<open>'a list \<Rightarrow> 'a \<Rightarrow> (nat \<times> bool)\<close> where
\<open>pos_in_list L a = (fold (\<lambda> a' (c, b). if(\<not> b) then (if(a'=a) then (c, True) else (c+1, False))
     else (c,b) ) L (0, False))\<close>

fun manufactured_assignment :: \<open>nat list \<Rightarrow> 'v list \<Rightarrow> 'v assignment\<close> where
\<open>manufactured_assignment varList valList = 
 (\<lambda> M. if (M \<in> set varList)
       then valList ! fst (pos_in_list (sort varList) M) else undefined) \<close>

fun value_fm' :: \<open>('v, 'mybool) scheme \<Rightarrow> 'v list \<Rightarrow> ('v, 'a, 'b, 'c, 'mybool) model \<Rightarrow> ('a, 'b, 'c) fm \<Rightarrow> 'mybool\<close> where
"value_fm' S val_list (D, Cw, Fw, Rw) f
 = ( if (length val_list = length (freevarL f))
     then value_fm S (manufactured_assignment (freevarL f) val_list)
      (D, Cw, Fw, Rw) f else undefined )"

lemma value_fm'_test1:
 "value_fm' \<tau> [2, 2, 1::nat] (D, Cw, Fw, Rw) (And (Equ (Var 10) (Var 2))
    (Equ (Var 10) (Var 3))) = f2" by simp

lemma value_fm'_test2:
 "value_fm' \<tau> [2, 2, 2::nat] (D, Cw, Fw, Rw) (And (Equ (Var 10) (Var 2))
    (Equ (Var 10) (Var 3))) = t2" by simp

fun signification :: \<open>('v, 'mybool) scheme
   \<Rightarrow> ('v, 'a, 'b, 'c, 'mybool) model \<Rightarrow> ('a, 'b, 'c) fm 
    \<Rightarrow> ('v list \<Rightarrow> 'mybool)\<close> where
"signification S Mod fm = (\<lambda> value_list. value_fm' S value_list Mod fm)"

fun extension :: \<open> ('v, ('mybool :: order)) scheme
   \<Rightarrow> ('v, 'a, 'b, 'c, 'mybool) model \<Rightarrow> ('a, 'b, 'c) fm 
    \<Rightarrow> ('v list set)\<close> where
"extension (myFalse, myTrue, myNot, myAnd, myUni) Mod fm
    = {vl :: 'v list. myTrue \<le> (signification (myFalse, myTrue, myNot, myAnd, myUni) Mod fm vl)}"

fun antiextension :: \<open> ('v, ('mybool :: order)) scheme
   \<Rightarrow> ('v, 'a, 'b, 'c, 'mybool) model \<Rightarrow> ('a, 'b, 'c) fm 
    \<Rightarrow> ('v list set)\<close> where
"antiextension (myFalse, myTrue, myNot, myAnd, myUni) Mod fm
    = {vl :: 'v list. myFalse \<le> (signification (myFalse, myTrue, myNot, myAnd, myUni) Mod fm vl)}"

subsection \<open>Substitutions\<close>
text \<open>subst\_term tm n t1 $\equiv$ in the term tm replace all occurences of variable n 
   with the term t1 \<close>
fun subst_term :: "('a, 'b) tm \<Rightarrow> nat \<Rightarrow> ('a, 'b) tm \<Rightarrow> ('a, 'b) tm" where
"(subst_term (Var n) (m ::nat) t1) = (if n = m then t1 else (Var n) )" |
"(subst_term (Const c) m t1) = (Const c)" |
"(subst_term (Fun f_symb term_list)  m t1) =
   (Fun f_symb ((map (\<lambda> x. subst_term x m t1) term_list)) )"

fun subst_termS :: "('a, 'b) tm \<Rightarrow> (nat \<Rightarrow> ('a, 'b) tm) \<Rightarrow> ('a, 'b) tm" where
"subst_termS (Var n) \<theta> = \<theta> n" |
"subst_termS (Const c) \<theta> = (Const c)" |
"subst_termS (Fun f_symb term_list) \<theta> =
   (Fun f_symb ((map (\<lambda> x. subst_termS x \<theta>) term_list)) )"

abbreviation \<iota>:: "nat \<Rightarrow> ('a, 'b) tm" where
\<open>\<iota> \<equiv> (\<lambda> n. Var n)\<close>

lemma subst_termS_test: "subst_termS A (\<iota> (n := t)) = subst_term A n t"
  by(induction A; simp)

lemma subst_term_test:
 \<open>subst_term ( Fun f [Const c1, Var 1, Var 3]) 3 (Const c2)
  =  ( Fun f [Const c1, Var 1, Const c2])\<close> by simp

lemma subst_term_on_closedt_is_id: 
"freevar_tm tm = {} \<Longrightarrow> (subst_term tm x t) = tm"
  by(induction tm; simp add:map_idI)

lemma subst_term_is_id2:
"x \<notin> freevar_tm tm \<Longrightarrow> (subst_term tm x t) = tm"
  by(induction tm; simp add:map_idI)

fun updt_w_subst :: \<open>(('v, 'a,'b,'c) const_mod \<times> ('v, 'a,'b,'c) func_mod) 
  \<Rightarrow> 'v assignment \<Rightarrow> (nat \<Rightarrow> ('a, 'b) tm) \<Rightarrow> 'v assignment\<close> where
"updt_w_subst (Cw, Fw) w \<theta>  = (\<lambda> m. value_tm w (Cw, Fw) (\<theta> m))"

lemma updt_w_subst_is_id:
\<open> \<theta> m = Var m \<Longrightarrow> (updt_w_subst (Cw, Fw) w \<theta>) m = w m\<close> by simp

lemma substitution_theoremT:
\<open>value_tm w (Cw, Fw) (subst_termS t \<theta>)
   = value_tm (updt_w_subst (Cw, Fw) w \<theta>) (Cw, Fw) t\<close>
  apply(induction t; simp) by (smt comp_apply map_eq_conv)

fun substu where
"substu x t f =
  (if (x \<notin> freevar_tm t) then x
    else Min {v. (v \<notin> freevar_tm t) \<and> (v \<notin> contvar f)} )"

fun qtrg :: \<open>('a, 'b, 'c) fm \<Rightarrow> nat\<close> where
"qtrg (Rel Rs tml) = 0" |
"qtrg (Equ tm1 tm2) = 0" |
"qtrg (And fm1 fm2) = Max {qtrg fm1, qtrg fm2} +1" |
"qtrg (Neg fm1) = qtrg fm1 +1" |
"qtrg Fal = 0" |
"qtrg (Forall var A) = qtrg A +10 "

abbreviation do_sub where
"do_sub N x phi \<theta> \<equiv> (N \<in> freevar (Forall x phi) \<and> Var N \<noteq> \<theta> N)"

fun substuS where
"substuS x phi \<theta> =
  (if (\<forall> m. (do_sub m x phi \<theta>) \<longrightarrow> x \<notin> freevar_tm (\<theta> m)) then x
    else Inf {v. (\<forall> m. (do_sub m x phi \<theta>) \<longrightarrow> v \<notin> freevar_tm (\<theta> m))
           \<and> (v \<notin> contvar phi)})"

abbreviation bounded where
"bounded \<theta> \<equiv> (\<exists> n. \<forall> N >n. \<theta> N = Var N)"

lemma finite_freevar_tm:\<open>finite (freevar_tm t)\<close>
  by(induction t; simp)

lemma finite_contvar:\<open>finite (contvar phi)\<close>
  by(induction phi; simp; metis List.finite_set freevar_tm_id)

lemma finite_bounded: \<open>\<lbrakk> finite (A :: nat set) \<rbrakk>
    \<Longrightarrow> \<exists> n. \<forall> N > n. N \<notin> A\<close>
  proof(cases "A ={}")
    case True
    then show ?thesis by simp
  next
    case False
    assume \<open>finite A\<close>  
    from this False have "\<forall> N > Max A. N \<notin> A" by auto
    then show ?thesis by(rule exI)
  qed

lemma bounded_contvar:\<open>\<exists> n. \<forall> N > n. N \<notin> (contvar phi)\<close>
  using finite_contvar finite_bounded by auto

lemma bounded_finite: \<open>\<lbrakk> \<exists> n. \<forall> N > n. N \<notin> (A :: nat set) \<rbrakk>
    \<Longrightarrow> finite A\<close>
proof-
  fix A :: \<open>nat set\<close>
  assume H: " \<exists> n. \<forall> N > n. N \<notin> A"
  then obtain n where Hn: \<open>\<forall> N > n. N \<notin> A\<close> by auto

  have A: " finite {n'. n' \<le> n}" using finite_Collect_le_nat by simp
  have B: "A \<subseteq> {n'. n' \<le> n}" using Hn
    by (metis mem_Collect_eq not_le_imp_less subsetI)

  from A B show "finite A" using finite_subset by auto
qed

lemma substuS_notin_freevar_tm:
   \<open>\<lbrakk> bounded \<theta>; do_sub m x phi \<theta> \<rbrakk>
\<Longrightarrow> (substuS x phi \<theta>) \<notin> freevar_tm (\<theta> m)\<close>
proof(cases "(\<forall> m. (do_sub m x phi \<theta>) \<longrightarrow> x \<notin> freevar_tm (\<theta> m))")
  case True
  then have I: "substuS x phi \<theta> = x" by simp
  assume "do_sub m x phi \<theta>"
  then have "x \<notin> freevar_tm (\<theta> m)" using True by blast
  then show "(substuS x phi \<theta>) \<notin> freevar_tm (\<theta> m)" using I by simp
next
  case False
  let ?newu = "Inf {v. (\<forall> m. (do_sub m x phi \<theta>) \<longrightarrow> v \<notin> freevar_tm (\<theta> m))
           \<and> (v \<notin> contvar phi)}"
  assume \<open>bounded \<theta>\<close>
  then have A: "finite {m. \<theta> m \<noteq> \<iota> m}" using bounded_finite by simp
  have \<open>{m. do_sub m x phi \<theta>} \<subseteq> {m. \<theta> m \<noteq> \<iota> m}\<close> by auto
  then have A': \<open>finite {m. do_sub m x phi \<theta>}\<close>
    using A finite_subset by auto
  
  have B: "\<forall> m . finite (freevar_tm (\<theta> m))" using finite_freevar_tm by auto

  let ?S = \<open>{m'. \<exists> m. (do_sub m x phi \<theta>) \<and> m' \<in> freevar_tm (\<theta> m)}\<close>
  have \<open>?S = \<Union> { freevar_tm (\<theta> m) | m. do_sub m x phi \<theta>}\<close> by auto
  from this A' B have \<open>finite ?S\<close>
    using finite_Union by auto
  hence \<open>finite {m'. \<not> (\<forall> m. (do_sub m x phi \<theta>) \<longrightarrow> m' \<notin> freevar_tm (\<theta> m))}\<close> by simp
  hence
  " \<exists> n. \<forall> N > n. N \<notin> {m'. \<not> (\<forall> m. (do_sub m x phi \<theta>) \<longrightarrow> m' \<notin> freevar_tm (\<theta> m))}"
    by(rule finite_bounded)
  then obtain n1 where Hn1:
  "\<forall> N > n1. (\<forall> m. (do_sub m x phi \<theta>) \<longrightarrow> N \<notin> freevar_tm (\<theta> m))"
    by auto

  from bounded_contvar have "\<exists> n2. \<forall> N > n2. N \<notin> contvar phi" by auto
  then obtain n2 where Hn2: "\<forall> N > n2. N \<notin> contvar phi" by auto
  
  let ?N = "Max{n1, n2} +1"
  from Hn1 have A: \<open>(\<forall> m. (do_sub m x phi \<theta>) \<longrightarrow> ?N \<notin> freevar_tm (\<theta> m))\<close> by auto
  from Hn2 have B: \<open>?N \<notin> contvar phi\<close> by auto

  from Hn1 Hn2 have "?N \<in> {v. (\<forall> m. (do_sub m x phi \<theta>) \<longrightarrow> v \<notin> freevar_tm (\<theta> m))
           \<and> (v \<notin> contvar phi)}" by simp
  then have "{v. (\<forall> m. (do_sub m x phi \<theta>) \<longrightarrow> v \<notin> freevar_tm (\<theta> m))
           \<and> (v \<notin> contvar phi)} \<noteq> {}" by auto
  then have P: "(\<forall> m. (do_sub m x phi \<theta>) \<longrightarrow> ?newu \<notin> freevar_tm (\<theta> m))
           \<and> (?newu \<notin> contvar phi)" using Inf_nat_def1
    by (smt mem_Collect_eq)
  assume "do_sub m x phi \<theta>"
  then have "?newu \<notin> freevar_tm (\<theta> m)" using P by simp
  then show ?thesis using False by auto
qed

lemma substuS\<iota>_is_id: "substuS x phi \<iota> = x" by simp
lemma substuSxx_is_id: "substuS x phi (\<iota> (x := tm)) = x" by simp

fun subst\<theta>S where
"subst\<theta>S x phi \<theta> = ( \<lambda> N. if(do_sub N x phi \<theta>) then \<theta> N
   else if N = x then Var (substuS x phi \<theta>) else Var N)"

lemma subst\<theta>Sxx_is_id: "subst\<theta>S x phi (\<iota> (x := tm)) = \<iota>"
  by( simp add:substuSxx_is_id; auto)

lemma subst\<theta>S\<iota>_is_id: "subst\<theta>S x phi \<iota> = \<iota>"
  by(simp add: substuS\<iota>_is_id; auto)

fun subst_formS :: "('a, 'b, 'c) fm \<Rightarrow> (nat \<Rightarrow> ('a, 'b) tm) \<Rightarrow> ('a, 'b, 'c) fm" where
"subst_formS (Rel Rsymb tml) \<theta> = Rel Rsymb (map (\<lambda> x. subst_termS x \<theta>) tml )" |
"subst_formS (Equ tm1 tm2) \<theta> = Equ (subst_termS tm1 \<theta>) (subst_termS tm2 \<theta>)" |
"subst_formS Fal \<theta> = Fal" |
"subst_formS (And fm1 fm2) \<theta> = And (subst_formS fm1 \<theta>) (subst_formS fm2 \<theta>)" |
"subst_formS (Neg f) \<theta> = Neg (subst_formS f \<theta>)" |
"subst_formS (Forall x phi) \<theta> = Forall (substuS x phi \<theta>)
        (subst_formS phi (subst\<theta>S x phi \<theta>) )"

lemma subst_termS_\<iota>_is_id: "(subst_termS tm \<iota>) = tm" 
  by(induction tm; simp add: map_idI)

lemma subst_formS_\<iota>_is_id:"(subst_formS phi \<iota>) = phi"
proof(induction phi)
case (Rel x1 x2)
  then show ?case by(simp add: subst_termS_\<iota>_is_id)
next
case (Equ x1 x2)
  then show ?case by(simp add: subst_termS_\<iota>_is_id)
next
  case Fal
  then show ?case by auto
next
  case (And phi1 phi2)
  then show ?case by auto
next
  case (Neg phi)
  then show ?case by auto
next
  case (Forall x1 phi)
  have "subst_formS (Forall x1 phi) \<iota> = Forall x1
        (subst_formS phi (subst\<theta>S x1 phi \<iota>) )" by simp
  then have "subst_formS (Forall x1 phi) \<iota> = Forall x1
        (subst_formS phi \<iota> )" using subst\<theta>S\<iota>_is_id by (metis)
  then show ?case using Forall by simp
qed

lemma subst\<theta>S_bounded:
"bounded \<theta> \<Longrightarrow> bounded (subst\<theta>S var fm \<theta>)"
proof-
  assume \<open>bounded \<theta>\<close>
  then obtain n where "\<forall>N>n. \<theta> N = \<iota> N" by auto
  then have Hn: "\<forall> N >  n. do_sub N var fm \<theta> = False" by auto
  let ?n' = "Max {var +1, n}"
  from Hn have Hn': \<open>\<forall> N > ?n'. do_sub N var fm \<theta> = False \<and> N \<noteq> var\<close> by auto
  hence "\<forall> N > ?n'. subst\<theta>S var fm \<theta> N = \<iota> N" by simp
  thus "bounded (subst\<theta>S var fm \<theta>)" by(rule exI)
qed

lemma on_var_dont_sub:
  "do_sub m var fm \<theta> \<Longrightarrow> m \<noteq> var" by simp

lemma substitution_theoremF:
\<open> bounded \<theta> \<Longrightarrow>
value_fm (myFalse, myTrue, myNot, myAnd, myUni) w (D, Cw, Fw, Rw)
   (subst_formS fm \<theta>) = value_fm (myFalse, myTrue, myNot, myAnd, myUni)
   (updt_w_subst (Cw, Fw) w \<theta>) (D, Cw, Fw, Rw) fm\<close>
proof(induction fm arbitrary: w \<theta>)
let ?S = "(myFalse, myTrue, myNot, myAnd, myUni)"
  case (Rel Rsymb tmlist)
  have \<open>\<forall> tm \<in> set tmlist.
   (value_tm (\<lambda>m. value_tm w (Cw, Fw) (\<theta> m)) (Cw, Fw) tm
       = (value_tm w (Cw, Fw)) (subst_termS tm \<theta>))\<close> by (simp add: substitution_theoremT)
  then have Hi: "(map (value_tm w (Cw, Fw)) (map (\<lambda>x. subst_termS x \<theta>) tmlist)) = 
(map (value_tm (\<lambda>m. value_tm w (Cw, Fw) (\<theta> m)) (Cw, Fw)) tmlist)" by simp

  have \<open>value_fm ?S w (D, Cw, Fw, Rw) (subst_formS (Rel Rsymb tmlist) \<theta>)
    = value_fm ?S w (D, Cw, Fw, Rw) (Rel Rsymb (map (\<lambda>x. subst_termS x \<theta>) tmlist))\<close> by simp
  also have "... = Rw Rsymb (map (value_tm w (Cw, Fw))
     (map (\<lambda>x. subst_termS x \<theta>) tmlist))" by simp
  also have "\<dots> = Rw Rsymb (map (value_tm (\<lambda>m. value_tm w (Cw, Fw) (\<theta> m)) (Cw, Fw)) tmlist)"
    using Hi by metis
  also have "\<dots> = value_fm ?S (updt_w_subst (Cw, Fw) w \<theta>) (D, Cw, Fw, Rw) (Rel Rsymb tmlist)" by simp
  finally show ?case by simp
next
case (Equ x1 x2)
  then show ?case using substitution_theoremT
    subst_formS.simps(2) value_fm.simps(3) by smt
next
  case Fal
  then show ?case by simp
next
  case (And fm1 fm2)
  then show ?case by simp
next
  case (Neg fm)
  then show ?case by simp
next
  case (Forall var fm)
  let ?S = "(myFalse, myTrue, myNot, myAnd, myUni)"
  from Forall.IH have IH: "\<And> w \<theta>. (bounded \<theta>) \<Longrightarrow>
  value_fm ?S w (D, Cw, Fw, Rw) (subst_formS fm \<theta>) =
  value_fm ?S (updt_w_subst (Cw, Fw) w \<theta>) (D, Cw, Fw, Rw) fm" by simp

  fix w
  fix \<theta> :: \<open>nat \<Rightarrow> ('a,'b) tm\<close>
  assume \<open>bounded \<theta>\<close>
  hence Hbsubst\<theta>: "bounded (subst\<theta>S var fm \<theta>)" by(rule subst\<theta>S_bounded)
  have "value_fm ?S w (D, Cw, Fw, Rw) (subst_formS (Forall var fm) \<theta>)
      = value_fm ?S w (D, Cw, Fw, Rw) (Forall (substuS var fm \<theta>)
   (subst_formS fm (subst\<theta>S var fm \<theta>)))" by simp
  moreover have "... = myUni D (\<lambda> v. value_fm ?S (\<lambda>k. if k = (substuS var fm \<theta>)
  then v else w k) (D, Cw, Fw, Rw) (subst_formS fm (subst\<theta>S var fm \<theta>)))" by simp
  moreover have "... = myUni D (\<lambda> v. value_fm ?S (updt_w_subst (Cw, Fw)
   (\<lambda>k. if k = (substuS var fm \<theta>) then v else w k)
     (subst\<theta>S var fm \<theta>)) (D, Cw, Fw, Rw) fm)" using IH Hbsubst\<theta> by simp
  moreover have "... = myUni D (\<lambda> v. value_fm ?S ( \<lambda> m. value_tm
   (\<lambda>k. if k = (substuS var fm \<theta>) then v else w k) (Cw, Fw)
     ( subst\<theta>S var fm \<theta> m) ) (D, Cw, Fw, Rw) fm)" by simp
  ultimately have IdL: \<open>value_fm ?S w (D, Cw, Fw, Rw) (subst_formS (Forall var fm) \<theta>)
  = myUni D (\<lambda> v. value_fm ?S (\<lambda> m. value_tm
   (\<lambda>k. if k = (substuS var fm \<theta>) then v else w k) (Cw, Fw)
     ( subst\<theta>S var fm \<theta> m) ) (D, Cw, Fw, Rw) fm)\<close> by simp

  have IdM: "\<And> v. value_fm ?S (\<lambda> m. value_tm
   (\<lambda>k. if k = (substuS var fm \<theta>) then v else w k) (Cw, Fw)
     ( subst\<theta>S var fm \<theta> m) ) (D, Cw, Fw, Rw) fm
 = value_fm ?S (\<lambda> m. (if m \<noteq> var then value_tm
         w (Cw, Fw) (subst\<theta>S var fm \<theta> m) else v))
      (D, Cw, Fw, Rw) fm" proof-
  fix a
  let ?ws = "(\<lambda>k. if k = (substuS var fm \<theta>) then a else w k)"

  have "\<forall> m. value_tm ?ws (Cw, Fw) (subst\<theta>S var fm \<theta> m) 
    = ( if(m \<noteq> var) then value_tm ?ws (Cw, Fw) ( subst\<theta>S var fm \<theta> m)
       else a)" by auto
  hence Calc1: "value_fm ?S (\<lambda> m. value_tm ?ws (Cw, Fw)
     (subst\<theta>S var fm \<theta> m)) (D, Cw, Fw, Rw) fm
  = value_fm ?S (\<lambda> m. (if m \<noteq> var then value_tm
         ?ws (Cw, Fw) (subst\<theta>S var fm \<theta> m) else a))
      (D, Cw, Fw, Rw) fm" by simp

  let ?w1 = "(\<lambda> m. (if m \<noteq> var then value_tm
         ?ws (Cw, Fw) (subst\<theta>S var fm \<theta> m) else a))"
  let ?w2 = "(\<lambda> m. (if m \<noteq> var then value_tm
         w (Cw, Fw) (subst\<theta>S var fm \<theta> m) else a))"

  have "\<forall>m. do_sub m var fm \<theta> \<longrightarrow>
  value_tm ?ws (Cw, Fw) (subst\<theta>S var fm \<theta> m) =
  value_tm w (Cw, Fw) (subst\<theta>S var fm \<theta> m)"
  proof
    fix m
    show "do_sub m var fm \<theta> \<longrightarrow> value_tm ?ws (Cw, Fw) (subst\<theta>S var fm \<theta> m) = value_tm w (Cw, Fw) (subst\<theta>S var fm \<theta> m)" proof
      assume "do_sub m var fm \<theta>"
      hence Hu: "substuS var fm \<theta> \<notin> freevar_tm (\<theta> m)" using \<open>bounded \<theta>\<close>  by(metis substuS_notin_freevar_tm)
      have "\<And> m'. ?ws m' \<noteq> w m' \<Longrightarrow> m' = (substuS var fm \<theta>)" by metis
      hence Coinc_loc:
       "\<And> m'. m' \<noteq> (substuS var fm \<theta>) \<Longrightarrow> ?ws m' = w m'" by metis
      have "\<And> m'. m' \<in> freevar_tm (\<theta> m) \<Longrightarrow> m' \<noteq> (substuS var fm \<theta>)" using Hu by blast
      hence "\<And> m'. m' \<in> freevar_tm (\<theta> m) \<Longrightarrow> ?ws m' = w m'" using Coinc_loc by auto
      then have "\<forall>m'\<in>freevar_tm (\<theta> m). ?ws m' = w m'" by metis
      thus "value_tm ?ws (Cw, Fw) (subst\<theta>S var fm \<theta> m) =
            value_tm w (Cw, Fw) (subst\<theta>S var fm \<theta> m)"
        using value_tm_locdet[of "\<theta> m" "?ws" "w" "Cw" "Fw"]
        using \<open>do_sub m var fm \<theta>\<close> by auto
    qed
  qed
  from this have Coinc1:
    "\<forall>m. do_sub m var fm \<theta> \<longrightarrow> ?w1 m = ?w2 m" by simp
  have Coinc2: "?w1 var = ?w2 var" by simp

  have A: "\<forall>m. \<not> do_sub m var fm \<theta> \<longrightarrow> m \<noteq> var
   \<longrightarrow> ?w1 m = ?ws m" by simp
  have B: "\<forall>m. \<not> do_sub m var fm \<theta> \<longrightarrow> m \<noteq> var
   \<longrightarrow> ?w2 m = w m" by simp
  have C: "\<forall>m. w m \<noteq> ?ws m \<longrightarrow> m = substuS var fm \<theta>" by simp

  have "\<forall> m. \<not> do_sub m var fm \<theta> \<longrightarrow> m \<noteq> var
  \<longrightarrow> ?w1 m \<noteq> ?w2 m \<longrightarrow> m=substuS var fm \<theta>"
  proof
    fix m show " \<not> do_sub m var fm \<theta> \<longrightarrow> m \<noteq> var 
  \<longrightarrow> ?w1 m \<noteq> ?w2 m \<longrightarrow> m=substuS var fm \<theta>"
    proof assume H1: "\<not> do_sub m var fm \<theta>" show
" m \<noteq> var \<longrightarrow> ?w1 m \<noteq> ?w2 m \<longrightarrow> m=substuS var fm \<theta>" proof
   assume H2: "m \<noteq> var" show "?w1 m \<noteq> ?w2 m \<longrightarrow> m=substuS var fm \<theta>" proof
     assume H3: "?w1 m \<noteq> ?w2 m "
     from H1 H2 A have D: "?w1 m = ?ws m" by simp
     from H1 H2 B have E: "?w2 m = w m" by simp
     from D E H3 have \<open>?ws m \<noteq> w m\<close> by simp
     then have F: "w m \<noteq> ?ws m" by(rule not_sym)
     from C have "w m \<noteq> (if m = substuS var fm \<theta>
         then a else w m) \<longrightarrow> m = substuS var fm \<theta>" by(rule allE)
     from F this show "m=substuS var fm \<theta>" by auto
   qed
 qed
qed
qed
  then have Coinc3: "\<forall> m. \<not> do_sub m var fm \<theta> \<longrightarrow> m \<noteq> var
  \<longrightarrow> m \<noteq> substuS var fm \<theta> \<longrightarrow> ?w1 m = ?w2 m" by simp

  from Coinc1 Coinc2 Coinc3 have Coinc: "\<forall> m.
    m \<noteq> substuS var fm \<theta> \<longrightarrow> ?w1 m = ?w2 m" by blast

  have Fact: "substuS var fm \<theta> \<noteq> var \<Longrightarrow>
      substuS var fm \<theta> \<notin> contvar fm"
  proof-
    assume H: "substuS var fm \<theta> \<noteq> var"
    let ?newu = "Inf {v. (\<forall> m. (do_sub m var fm \<theta>) \<longrightarrow> v \<notin> freevar_tm (\<theta> m))
           \<and> (v \<notin> contvar fm)}"
    from H have Id1: "substuS var fm \<theta> = ?newu" by auto
  
    from \<open>bounded \<theta>\<close> have A: "finite {m. \<theta> m \<noteq> \<iota> m}" using bounded_finite by simp
    have \<open>{m. do_sub m var fm \<theta>} \<subseteq> {m. \<theta> m \<noteq> \<iota> m}\<close> by auto
    then have A': \<open>finite {m. do_sub m var fm \<theta>}\<close>
    using A finite_subset by auto
  
    have B: "\<forall> m . finite (freevar_tm (\<theta> m))" using finite_freevar_tm by auto

    let ?S = \<open>{m'. \<exists> m. (do_sub m var fm \<theta>) \<and> m' \<in> freevar_tm (\<theta> m)}\<close>
    have \<open>?S = \<Union> { freevar_tm (\<theta> m) | m. do_sub m var fm \<theta>}\<close> by auto
    from this A' B have \<open>finite ?S\<close>
    using finite_Union by auto
    hence \<open>finite {m'. \<not> (\<forall> m. (do_sub m var fm \<theta>) \<longrightarrow> m' \<notin> freevar_tm (\<theta> m))}\<close> by simp
    hence
      " \<exists> n. \<forall> N > n. N \<notin> {m'. \<not> (\<forall> m. (do_sub m var fm \<theta>) \<longrightarrow> m' \<notin> freevar_tm (\<theta> m))}"
      by(rule finite_bounded)
    then obtain n1 where Hn1:
      "\<forall> N > n1. (\<forall> m. (do_sub m var fm \<theta>) \<longrightarrow> N \<notin> freevar_tm (\<theta> m))"
      by auto

    from bounded_contvar have "\<exists> n2. \<forall> N > n2. N \<notin> contvar fm" by auto
    then obtain n2 where Hn2: "\<forall> N > n2. N \<notin> contvar fm" by auto
  
    let ?N = "Max{n1, n2} +1"
    from Hn1 have A: \<open>(\<forall> m. (do_sub m var fm \<theta>) \<longrightarrow> ?N \<notin> freevar_tm (\<theta> m))\<close> by auto
    from Hn2 have B: \<open>?N \<notin> contvar fm\<close> by auto

    from Hn1 Hn2 have "?N \<in> {v. (\<forall> m. (do_sub m var fm \<theta>) \<longrightarrow> v \<notin> freevar_tm (\<theta> m))
           \<and> (v \<notin> contvar fm)}" by simp
    then have "{v. (\<forall> m. (do_sub m var fm \<theta>) \<longrightarrow> v \<notin> freevar_tm (\<theta> m))
           \<and> (v \<notin> contvar fm)} \<noteq> {}" by auto
    then have P: "(\<forall> m. (do_sub m var fm \<theta>) \<longrightarrow> ?newu \<notin> freevar_tm (\<theta> m))
           \<and> (?newu \<notin> contvar fm)" using Inf_nat_def1
    by (smt mem_Collect_eq)
  then have "?newu \<notin> contvar fm" using P by simp
  thus "substuS var fm \<theta> \<notin> contvar fm" using Id1 by auto
qed
  
  have P1: "substuS var fm \<theta> \<noteq> var \<Longrightarrow>
  value_fm ?S ?w1 (D, Cw, Fw, Rw) fm = value_fm ?S ?w2 (D, Cw, Fw, Rw) fm"
  proof-
    assume H: "substuS var fm \<theta> \<noteq> var"
  have " \<forall>m\<in>contvar fm. ?w1 m = ?w2 m" proof
    fix m
    assume "m \<in> contvar fm"
    from this Fact H have "m \<noteq> substuS var fm \<theta>" by blast
    then show "?w1 m = ?w2 m" using Coinc by simp
  qed
  then show "value_fm ?S ?w1 (D, Cw, Fw, Rw) fm = value_fm ?S ?w2 (D, Cw, Fw, Rw) fm"
    using value_fm_locdetS_cont[of "fm" "?w1" "?w2"] by simp
qed

have P2: "substuS var fm \<theta> = var \<Longrightarrow>
  value_fm ?S ?w1 (D, Cw, Fw, Rw) fm = value_fm ?S ?w2 (D, Cw, Fw, Rw) fm" 
 by (metis (no_types, lifting) \<open>\<forall>m. \<not> (m \<in> freevar (Forall var fm) \<and> \<iota> m \<noteq> \<theta> m) \<longrightarrow> m \<noteq> var \<longrightarrow> (if m \<noteq> var then value_tm (\<lambda>k. if k = substuS var fm \<theta> then a else w k) (Cw, Fw) (subst\<theta>S var fm \<theta> m) else a) \<noteq> (if m \<noteq> var then value_tm w (Cw, Fw) (subst\<theta>S var fm \<theta> m) else a) \<longrightarrow> m = substuS var fm \<theta>\<close> \<open>\<forall>m. m \<in> freevar (Forall var fm) \<and> \<iota> m \<noteq> \<theta> m \<longrightarrow> value_tm (\<lambda>k. if k = substuS var fm \<theta> then a else w k) (Cw, Fw) (subst\<theta>S var fm \<theta> m) = value_tm w (Cw, Fw) (subst\<theta>S var fm \<theta> m)\<close>)
  from P1 P2 have
   "value_fm ?S ?w1 (D, Cw, Fw, Rw) fm = value_fm ?S ?w2 (D, Cw, Fw, Rw) fm" by auto

  from this Calc1 show
    "value_fm ?S (\<lambda> m. value_tm ?ws (Cw, Fw)
     (subst\<theta>S var fm \<theta> m)) (D, Cw, Fw, Rw) fm = 
    value_fm ?S (\<lambda> m. (if m \<noteq> var then value_tm
         w (Cw, Fw) (subst\<theta>S var fm \<theta> m) else a))
      (D, Cw, Fw, Rw) fm" by simp
qed

  have Helper_right: "\<And> a. value_fm ?S (\<lambda>k. if k = var then a
     else (\<lambda>m. value_tm w (Cw, Fw) (\<theta> m)) k) (D, Cw, Fw, Rw) fm
       = value_fm ?S (\<lambda> m. (if m \<noteq> var then value_tm
         w (Cw, Fw) (subst\<theta>S var fm \<theta> m) else a))
      (D, Cw, Fw, Rw) fm"
  by (smt DiffI freevar.simps(6) singletonD subst\<theta>S.elims value_fm_locdetS)

  have "value_fm ?S (updt_w_subst (Cw, Fw) w \<theta>) (D, Cw, Fw, Rw) (Forall var fm)
  = value_fm ?S (\<lambda>m. value_tm w (Cw, Fw) (\<theta> m)) (D, Cw, Fw, Rw) (Forall var fm)" by simp
  moreover have "... = myUni D (\<lambda> v. value_fm ?S (\<lambda>k. if k = var then v
     else (\<lambda>m. value_tm w (Cw, Fw) (\<theta> m)) k) (D, Cw, Fw, Rw) fm)" by simp
  moreover have "... = myUni D (\<lambda> v.
      value_fm ?S (\<lambda> m. (if m \<noteq> var then value_tm
         w (Cw, Fw) (subst\<theta>S var fm \<theta> m) else v))
      (D, Cw, Fw, Rw) fm)" using Helper_right by simp
  ultimately have IdR: "value_fm ?S (updt_w_subst (Cw, Fw) w \<theta>) (D, Cw, Fw, Rw) (Forall var fm)
= myUni D (\<lambda> v. value_fm ?S (\<lambda> m. (if m \<noteq> var then value_tm
  w (Cw, Fw) (subst\<theta>S var fm \<theta> m) else v)) (D, Cw, Fw, Rw) fm)" by simp

  from IdL IdR IdM show "value_fm ?S w (D, Cw, Fw, Rw) (subst_formS (Forall var fm) \<theta>) =
value_fm ?S (updt_w_subst (Cw, Fw) w \<theta>) (D, Cw, Fw, Rw) (Forall var fm)" by simp
qed

fun subst_form :: \<open>('a, 'b, 'c) fm \<Rightarrow> nat \<Rightarrow> ('a, 'b) tm \<Rightarrow> ('a, 'b, 'c) fm\<close> where
"subst_form fm n tm = subst_formS fm (\<iota> (n := tm))"

lemma subst_form_xx_is_id:
\<open>subst_form (Forall x phi) x tm = Forall x phi\<close>
proof-
  have "subst_formS (Forall x phi) (\<iota> (x := tm)) = 
        Forall (substuS x phi (\<iota> (x := tm)))
        (subst_formS phi (subst\<theta>S x phi (\<iota> (x := tm))) )" by simp
  then have "subst_formS (Forall x phi) (\<iota> (x := tm)) = 
        Forall x (subst_formS phi (subst\<theta>S x phi (\<iota> (x := tm))) )" by(simp add:substuSxx_is_id)
  then have "subst_formS (Forall x phi) (\<iota> (x := tm)) = 
        Forall x (subst_formS phi \<iota>)" using subst\<theta>Sxx_is_id by metis
  then show "subst_form (Forall x phi) x tm = 
        Forall x phi" using subst_formS_\<iota>_is_id by simp
qed

lemma subst_form_is_id: 
"x \<notin> contvar fm \<Longrightarrow> (subst_form fm x t) = fm"
proof(induction fm arbitrary: x)
  case (Rel Rs tl)
  from \<open>x \<notin> contvar (Rel Rs tl)\<close> freevar_contvar have \<open>x \<notin> freevar (Rel Rs tl)\<close> by auto
  from \<open>x \<notin> freevar (Rel Rs tl)\<close> have \<open>\<forall> tm \<in> set tl. x \<notin> freevar_tm tm\<close> by simp
  then have \<open>\<forall> tm \<in> set tl. subst_term tm x t = tm\<close> using subst_term_is_id2 by blast
  then show ?case by (simp add: map_idI subst_termS_test)
next
  case (Equ tm1 tm2)
  from this have A: \<open>x \<notin> freevar_tm tm1\<close> and B: \<open>x \<notin> freevar_tm tm2\<close> by auto
  from A have 1: \<open>subst_term tm1 x t = tm1\<close> using subst_term_is_id2 by blast
  from B have 2: \<open>subst_term tm2 x t = tm2\<close> using subst_term_is_id2 by blast
  from 1 2 show ?case by (simp add: subst_termS_test)
next
  case Fal
  then show ?case by simp
next
  case (And fm1 fm2)
  then show ?case by simp
next
  case (Neg fm)
  then show ?case by simp
next
  case (Forall var fm)
  from this have H: "x \<notin> contvar (Forall var fm)" by auto
  show ?case proof(cases "x = var")
    case True
    then show ?thesis using subst_form_xx_is_id by auto
  next
    case False
    have "subst_form (Forall var fm) x t
      = subst_formS (Forall var fm) (\<iota> (x := t))" by simp
    have up: "substuS var fm (\<iota> (x := t)) = var" 
      using H freevar_contvar by auto
    then have \<theta>p: "subst\<theta>S var fm (\<iota> (x := t)) = \<iota>" using H freevar_contvar by fastforce
    show ?thesis using Forall.IH up \<theta>p subst_formS_\<iota>_is_id by auto
  qed
qed

subsection \<open>Further small definitions\<close>
fun is_true_of :: \<open>('a, 'b, 'c) fm \<Rightarrow> 'v list 
\<Rightarrow> ('v, 'a,'b,'c, 'mybool ::order) model \<Rightarrow> ('v, 'mybool) scheme \<Rightarrow> bool\<close> where
"is_true_of A val_list (D, Cw, Fw, Rw) (myFalse, myTrue, myNot, myAnd, myUni)
 = (myTrue \<le> value_fm' (myFalse, myTrue, myNot, myAnd, myUni) val_list (D, Cw, Fw, Rw) A )"

fun is_false_of :: \<open>('a, 'b, 'c) fm \<Rightarrow> 'v list 
\<Rightarrow> ('v, 'a,'b,'c, 'mybool ::order) model \<Rightarrow> ('v, 'mybool) scheme \<Rightarrow> bool\<close> where
"is_false_of A val_list (D, Cw, Fw, Rw) (myFalse, myTrue, myNot, myAnd, myUni)
 = (myFalse \<le> value_fm' (myFalse, myTrue, myNot, myAnd, myUni) val_list (D, Cw, Fw, Rw) A )"

lemma theorem2A12a: " \<lbrakk> length (freevarL B) = length (dbar :: 'v list)\<rbrakk>
  \<Longrightarrow> is_true_of A dbar (D, Cw, Fw, Rw) \<tau> \<or> is_false_of A dbar (D, Cw, Fw, Rw) \<tau>"
by (metis (full_types) bool2.exhaust is_false_of.simps is_true_of.simps leq2.simps(1) leq2.simps(2) less_eq_bool2_def)

lemma theorem2A12b: " \<lbrakk> length (freevarL B) = length (dbar :: 'v list)\<rbrakk>
  \<Longrightarrow> \<not> ( is_true_of A dbar (D, Cw, Fw, Rw) \<tau> \<and> is_false_of A dbar (D, Cw, Fw, Rw) \<tau>)"
by (metis (full_types) bool2.exhaust is_false_of.simps is_true_of.simps leq2.simps(3) leq2.simps(4) less_eq_bool2_def)

lemma theorem2A12c: " \<lbrakk> length (freevarL B) = length (dbar :: 'v list)\<rbrakk>
  \<Longrightarrow> \<not> ( is_true_of A dbar (D, Cw, Fw, Rw) \<kappa> \<and> is_false_of A dbar (D, Cw, Fw, Rw) \<kappa>)"
by (metis (full_types) bool3.exhaust is_false_of.simps is_true_of.simps leq3.simps(6) leq3.simps(7) leq3.simps(9) less_eq_bool3_def)

lemma theorem2A12d: " \<lbrakk> length (freevarL B) = length (dbar :: 'v list)\<rbrakk>
  \<Longrightarrow> \<not> ( is_true_of A dbar (D, Cw, Fw, Rw) \<mu> \<and> is_false_of A dbar (D, Cw, Fw, Rw) \<mu>)"
by (metis (full_types) bool3.exhaust is_false_of.simps is_true_of.simps leq3.simps(6) leq3.simps(7) leq3.simps(9) less_eq_bool3_def)

lemma theorem2A13a: "\<lbrakk> freevarL A = []; freevarL B = []\<rbrakk>
\<Longrightarrow> is_true_of (And A B) [] (D, Cw, Fw, Rw) \<tau> \<longleftrightarrow>
 (is_true_of A [] (D, Cw, Fw, Rw) \<tau> \<and> is_true_of B [] (D, Cw, Fw, Rw) \<tau>)"
proof-
  assume HA: "freevarL A = []"
  assume HB: "freevarL B = []"
  show "is_true_of (And A B) [] (D, Cw, Fw, Rw) \<tau> \<longleftrightarrow>
 (is_true_of A [] (D, Cw, Fw, Rw) \<tau> \<and> is_true_of B [] (D, Cw, Fw, Rw) \<tau>)"
  proof
    assume And_true: "is_true_of (And A B) [] (D, Cw, Fw, Rw) \<tau>"
    from HA HB have HAB: "freevarL (And A B) = []" by simp
    from And_true have And_true2: "value_fm' \<tau> [] (D, Cw, Fw, Rw) (And A B) = t2"
      by (metis (full_types) bool2.exhaust is_true_of.simps leq2.simps(4) less_eq_bool2_def)
    from HA HAB And_true2 have ResA: "value_fm' \<tau> [] (D, Cw, Fw, Rw) A = t2"
      using \<tau>_and.elims by auto
    from HB HAB And_true2 have ResB: "value_fm' \<tau> [] (D, Cw, Fw, Rw) B = t2"
      using \<tau>_and.elims by auto
    from ResA ResB show "(is_true_of A [] (D, Cw, Fw, Rw) \<tau> \<and> is_true_of B [] (D, Cw, Fw, Rw) \<tau>)"
      by simp
  next
    assume "is_true_of A [] (D, Cw, Fw, Rw) \<tau> \<and> is_true_of B [] (D, Cw, Fw, Rw) \<tau>"
    then have HA: "is_true_of A [] (D, Cw, Fw, Rw) \<tau>" and HB: " is_true_of B [] (D, Cw, Fw, Rw) \<tau>" by auto
    from HA have A_true: "value_fm' \<tau> [] (D, Cw, Fw, Rw) A = t2"
      by (metis (full_types) bool2.exhaust is_true_of.simps leq2.simps(4) less_eq_bool2_def)
    from HB have B_true: "value_fm' \<tau> [] (D, Cw, Fw, Rw) B = t2"
      by (metis (full_types) bool2.exhaust is_true_of.simps leq2.simps(4) less_eq_bool2_def)
    from A_true B_true have "value_fm' \<tau> [] (D, Cw, Fw, Rw) (And A B) = t2" by auto
    then show "is_true_of (And A B) [] (D, Cw, Fw, Rw) \<tau>" by simp
  qed
qed

lemma theorem2A13b: "\<lbrakk> freevarL A = []; freevarL B = []\<rbrakk>
\<Longrightarrow> is_true_of (And A B) [] (D, Cw, Fw, Rw) \<kappa> \<longleftrightarrow>
 (is_true_of A [] (D, Cw, Fw, Rw) \<kappa> \<and> is_true_of B [] (D, Cw, Fw, Rw) \<kappa>)"
proof-
  assume HA: "freevarL A = []"
  assume HB: "freevarL B = []"
  show "is_true_of (And A B) [] (D, Cw, Fw, Rw) \<kappa> \<longleftrightarrow>
 (is_true_of A [] (D, Cw, Fw, Rw) \<kappa> \<and> is_true_of B [] (D, Cw, Fw, Rw) \<kappa>)"
  proof
    assume And_true: "is_true_of (And A B) [] (D, Cw, Fw, Rw) \<kappa>"
    from HA HB have HAB: "freevarL (And A B) = []" by simp
    from And_true have And_true2: "value_fm' \<kappa> [] (D, Cw, Fw, Rw) (And A B) = t3"
      by (metis (full_types) bool3.exhaust is_true_of.simps leq3.simps(6) leq3.simps(7) less_eq_bool3_def)
    from HA HAB And_true2 have ResA: "value_fm' \<kappa> [] (D, Cw, Fw, Rw) A = t3"
      using \<kappa>_and.elims by auto
    from HB HAB And_true2 have ResB: "value_fm' \<kappa> [] (D, Cw, Fw, Rw) B = t3"
      using \<kappa>_and.elims by auto
    from ResA ResB show "(is_true_of A [] (D, Cw, Fw, Rw) \<kappa> \<and> is_true_of B [] (D, Cw, Fw, Rw) \<kappa>)"
      by simp
  next
    assume "is_true_of A [] (D, Cw, Fw, Rw) \<kappa> \<and> is_true_of B [] (D, Cw, Fw, Rw) \<kappa>"
    then have HA: "is_true_of A [] (D, Cw, Fw, Rw) \<kappa>" and HB: " is_true_of B [] (D, Cw, Fw, Rw) \<kappa>" by auto
    from HA have A_true: "value_fm' \<kappa> [] (D, Cw, Fw, Rw) A = t3"
      by (metis (full_types) bool3.exhaust is_true_of.simps leq3.simps(6) leq3.simps(7) less_eq_bool3_def)
    from HB have B_true: "value_fm' \<kappa> [] (D, Cw, Fw, Rw) B = t3"
      by (metis (full_types) bool3.exhaust is_true_of.simps leq3.simps(6) leq3.simps(7) less_eq_bool3_def)
    from A_true B_true have "value_fm' \<kappa> [] (D, Cw, Fw, Rw) (And A B) = t3" by auto
    then show "is_true_of (And A B) [] (D, Cw, Fw, Rw) \<kappa>" by simp
  qed
qed

section \<open>Definability of Truth\<close>
abbreviation sentences where
"sentences \<equiv> { fm. freevar fm = {}}"

fun ground_mod :: \<open>'mybool \<Rightarrow> 'mybool \<Rightarrow> ('v, 'a, 'b, 'c, 'mybool) model \<Rightarrow> 'c \<Rightarrow> (('a, 'b, 'c) fm \<Rightarrow> 'v) \<Rightarrow> bool\<close> where
"ground_mod myFalse myTrue (D, Cw, Fw, Rw) G c =
 ( (inj c \<and> c` sentences \<subseteq> D) \<and>
 ( \<forall> rsymb val_list. rsymb \<noteq> G\<longrightarrow> 
        Rw rsymb val_list \<in> {myTrue, myFalse}) )"

fun modplus :: \<open>('v, 'a, 'b, 'c, 'mybool) model \<Rightarrow> 'c \<Rightarrow> ('v \<Rightarrow> 'mybool) \<Rightarrow> ('v, 'a, 'b, 'c, 'mybool) model\<close>
  where
"modplus (D, Cw, Fw, Rw) G g = (D, Cw, Fw, Rw (G := (\<lambda> val_list. g (hd val_list)) ))"

fun jump :: \<open>('v, 'mybool) scheme \<Rightarrow> ('v, 'a, 'b, 'c, 'mybool) model
  \<Rightarrow> 'c \<Rightarrow> (('a, 'b, 'c) fm \<Rightarrow> 'v) \<Rightarrow> ('v \<Rightarrow> 'mybool) \<Rightarrow> ('v \<Rightarrow> 'mybool)\<close>
  where
"jump (myFalse, myTrue, myNot, myAnd, myUni) (D, Cw, Fw, Rw) G c g =
( if (ground_mod myFalse myTrue (D, Cw, Fw, Rw) G c) then
 (\<lambda> A. if (A \<in> c` sentences) then
   value_fm (myFalse, myTrue, myNot, myAnd, myUni) (\<lambda> x. undefined)
      (modplus (D, Cw, Fw, Rw) G g) (inv c A)
   else myFalse) else undefined)"

lemma Fact: \<open>\<lbrakk> ground_mod myFalse myTrue (D, Cw, Fw, Rw) G c;
     \<forall>d. d \<notin> c` sentences \<longrightarrow> g d = myFalse \<rbrakk>
\<Longrightarrow> (\<forall> d. jump (myFalse, myTrue, myNot, myAnd, myUni) (D, Cw, Fw, Rw) G c g d = g d)
\<longleftrightarrow> ( \<forall> A \<in> sentences.
   value_fm' (myFalse, myTrue, myNot, myAnd, myUni) []  (modplus (D, Cw, Fw, Rw) G g) A
 = value_fm' (myFalse, myTrue, myNot, myAnd, myUni) [c A] (modplus (D, Cw, Fw, Rw) G g) (Rel G [ Var 1 ]) )\<close>
proof-
  let ?S = "(myFalse, myTrue, myNot, myAnd, myUni)"

  assume GM: "ground_mod myFalse myTrue (D, Cw, Fw, Rw) G c"
  then have H2: \<open>c` sentences \<subseteq> D\<close> by simp
  assume H1: \<open>\<forall> d. d \<notin> c` sentences \<longrightarrow> g d = myFalse\<close>

  from value_fm_locdet
  have Locdet_fact:
    "\<And> s1 s2 A. A \<in> sentences \<longrightarrow> value_fm ?S s1 (D, Cw, Fw, Rw) A = value_fm ?S s1 (D, Cw, Fw, Rw) A" by simp
  have InD_fact: "\<forall> A \<in> sentences. c A \<in> D" using H2 by auto

  from Locdet_fact InD_fact have Id_helper:
   "\<forall> A \<in> sentences. jump ?S (D, Cw, Fw, Rw) G c g (c A)
    = value_fm ?S (\<lambda> x. undefined) (modplus (D, Cw, Fw, Rw) G g) A"
    using GM by simp

  have "\<forall> A \<in> sentences. freevarL A = []" using freevar_id by (smt mem_Collect_eq set_empty)
  then have "\<forall> A \<in> sentences.
   value_fm' ?S [] (modplus (D, Cw, Fw, Rw) G g) A
    = value_fm ?S (manufactured_assignment [] [])
      (modplus (D, Cw, Fw, Rw) G g) A" by auto
  then have "\<forall> A \<in> sentences. 
   value_fm' ?S [] (modplus (D, Cw, Fw, Rw) G g) A
  = value_fm ?S (\<lambda> x. undefined) (modplus (D, Cw, Fw, Rw) G g) A" using value_fm_locdet by simp
  then have Calculation1: "\<forall> A \<in> sentences.
   value_fm' ?S [] (modplus (D, Cw, Fw, Rw) G g) A 
  = jump ?S (D, Cw, Fw, Rw) G c g (c A)" using Id_helper by auto

  have Calculation2: "\<forall> A \<in> sentences.
   g (c A) = value_fm' ?S [c A] (modplus (D, Cw, Fw, Rw) G g) (Rel G [ Var 1 ])" by simp

  show \<open> (\<forall> d. jump (myFalse, myTrue, myNot, myAnd, myUni) (D, Cw, Fw, Rw) G c g d = g d)
\<longleftrightarrow> (\<forall> A \<in> sentences.
   value_fm' (myFalse, myTrue, myNot, myAnd, myUni) []  (modplus (D, Cw, Fw, Rw) G g) A
 = value_fm' (myFalse, myTrue, myNot, myAnd, myUni) [c A] (modplus (D, Cw, Fw, Rw) G g) (Rel G [ Var 1 ]) )\<close> proof
  assume "\<forall> d. jump (myFalse, myTrue, myNot, myAnd, myUni) (D, Cw, Fw, Rw) G c g d = g d"
  then have "\<forall> A \<in> sentences. jump ?S (D, Cw, Fw, Rw) G c g (c A) = g (c A)" using InD_fact by blast
  hence "\<forall> A \<in> sentences.
      value_fm' ?S [] (modplus (D, Cw, Fw, Rw) G g) A = g (c A)" using Calculation1 by simp
  thus "\<forall> A \<in> sentences.
      value_fm' ?S [] (modplus (D, Cw, Fw, Rw) G g) A = value_fm' ?S [c A] (modplus (D, Cw, Fw, Rw) G g) (Rel G [ Var 1 ])"
    using Calculation2 by metis
next
  assume "(\<forall> A \<in> sentences.
   value_fm' (myFalse, myTrue, myNot, myAnd, myUni) []  (modplus (D, Cw, Fw, Rw) G g) A
 = value_fm' (myFalse, myTrue, myNot, myAnd, myUni) [c A] (modplus (D, Cw, Fw, Rw) G g) (Rel G [ Var 1 ]) )"
  hence "\<forall> A \<in> sentences.
      value_fm' ?S [] (modplus (D, Cw, Fw, Rw) G g) A = g (c A)" using Calculation2 by metis
  hence "\<forall> A \<in> sentences. jump ?S (D, Cw, Fw, Rw) G c g (c A) = g (c A)" using Calculation1 by simp
  then have 1: "\<forall> d\<in>D. jump ?S (D, Cw, Fw, Rw) G c g d = g d" using H1 GM by auto
  have 2: "\<forall> d. d\<notin> D \<longrightarrow> jump ?S (D, Cw, Fw, Rw) G c g d = myFalse" using GM by auto
  have "\<forall> d. d\<notin> D \<longrightarrow>  d \<notin> c ` sentences" using H2 by auto
  then have 3: "\<forall> d. d\<notin>D \<longrightarrow> g d = myFalse" using H1 by simp
  show "\<forall> d. jump ?S (D, Cw, Fw, Rw) G c g d = g d" using 1 2 3
    by blast
qed
qed

lemma jump_\<mu>_monot: \<open> ground_mod f3 t3 (D, Cw, Fw, Rw) G c  \<Longrightarrow> f \<le> g
  \<Longrightarrow> jump \<mu> (D, Cw, Fw, Rw) G c f \<le> jump \<mu> (D, Cw, Fw, Rw) G c g\<close>
proof-
  assume GM: "ground_mod f3 t3 (D, Cw, Fw, Rw) G c"
  then have S: "c` sentences \<subseteq> D" by simp
  assume H: "f \<le> g"
  hence "Rw (G := (\<lambda> val_list. f (hd val_list)) )
       \<le> Rw (G := (\<lambda> val_list. g (hd val_list)) )"
    by (simp add: le_funD le_funI)

  then have "leqMod (modplus (D, Cw, Fw, Rw) G f) (modplus (D, Cw, Fw, Rw) G g)"
    by simp
  from this monot_in_\<mu> have Res: "\<And> s A.
    value_fm \<mu> s (modplus (D, Cw, Fw, Rw) G f) A
  \<le> value_fm \<mu> s (modplus (D, Cw, Fw, Rw) G g) A" by fastforce

  have "\<forall> A \<in> sentences.
    jump \<mu> (D, Cw, Fw, Rw) G c f (c A) \<le> jump \<mu> (D, Cw, Fw, Rw) G c g (c A)" proof
  fix A::"('c, 'b, 'd) fm"
  assume Asent: \<open>A \<in> sentences\<close>

  from S this have A: "jump \<mu> (D, Cw, Fw, Rw) G c f (c A) =
  value_fm \<mu> (\<lambda> x. undefined) (modplus (D, Cw, Fw, Rw) G f) A" using GM by simp

  from S Asent have B: "jump \<mu> (D, Cw, Fw, Rw) G c g (c A) =
  value_fm \<mu> (\<lambda> x. undefined) (modplus (D, Cw, Fw, Rw) G g) A" using GM by simp

  show "jump \<mu> (D, Cw, Fw, Rw) G c f (c A) \<le> jump \<mu> (D, Cw, Fw, Rw) G c g (c A)"
    using A B Res by simp
  qed
  from this have Res1: "\<forall> d \<in> c` sentences.
    jump \<mu> (D, Cw, Fw, Rw) G c f d \<le> jump \<mu> (D, Cw, Fw, Rw) G c g d" using GM by simp

  have A: "\<forall> d. d \<notin> c` sentences \<longrightarrow> jump \<mu> (D, Cw, Fw, Rw) G c f d = f3" using GM by simp
  have B: "\<forall> d. d \<notin> c` sentences \<longrightarrow> jump \<mu> (D, Cw, Fw, Rw) G c g d = f3" using GM by simp
  from A B have Res2: "\<forall> d. d \<notin> c` sentences \<longrightarrow> jump \<mu> (D, Cw, Fw, Rw) G c f d \<le> jump \<mu> (D, Cw, Fw, Rw) G c g d" by simp
  
  have "\<forall> d. jump \<mu> (D, Cw, Fw, Rw) G c f d \<le> jump \<mu> (D, Cw, Fw, Rw) G c g d"
    using Res1 Res2 by smt
  then show "jump \<mu> (D, Cw, Fw, Rw) G c f \<le> jump \<mu> (D, Cw, Fw, Rw) G c g"
    using le_funI by blast
qed

lemma jump_\<kappa>_monot: \<open> ground_mod f3 t3 (D, Cw, Fw, Rw) G c  \<Longrightarrow> f \<le> g
  \<Longrightarrow> jump \<kappa> (D, Cw, Fw, Rw) G c f \<le> jump \<kappa> (D, Cw, Fw, Rw) G c g\<close>
proof-
  assume GM: "ground_mod f3 t3 (D, Cw, Fw, Rw) G c"
  then have S: "c` sentences \<subseteq> D" by simp
  assume H: "f \<le> g"
  hence "Rw (G := (\<lambda> val_list. f (hd val_list)) )
       \<le> Rw (G := (\<lambda> val_list. g (hd val_list)) )"
    by (simp add: le_funD le_funI)

  then have "leqMod (modplus (D, Cw, Fw, Rw) G f) (modplus (D, Cw, Fw, Rw) G g)"
    by simp
  from this monot_in_\<kappa> have Res: "\<And> s A.
    value_fm \<kappa> s (modplus (D, Cw, Fw, Rw) G f) A
  \<le> value_fm \<kappa> s (modplus (D, Cw, Fw, Rw) G g) A" by fastforce

  have "\<forall> A \<in> sentences.
    jump \<kappa> (D, Cw, Fw, Rw) G c f (c A) \<le> jump \<kappa> (D, Cw, Fw, Rw) G c g (c A)" proof
  fix A::"('c, 'b, 'd) fm"
  assume Asent: \<open>A \<in> sentences\<close>

  from S this have A: "jump \<kappa> (D, Cw, Fw, Rw) G c f (c A) =
  value_fm \<kappa> (\<lambda> x. undefined) (modplus (D, Cw, Fw, Rw) G f) A" using GM by simp

  from S Asent have B: "jump \<kappa> (D, Cw, Fw, Rw) G c g (c A) =
  value_fm \<kappa> (\<lambda> x. undefined) (modplus (D, Cw, Fw, Rw) G g) A" using GM by simp

  show "jump \<kappa> (D, Cw, Fw, Rw) G c f (c A) \<le> jump \<kappa> (D, Cw, Fw, Rw) G c g (c A)"
    using A B Res by simp
  qed
  from this have Res1: "\<forall> d \<in> c` sentences.
    jump \<kappa> (D, Cw, Fw, Rw) G c f d \<le> jump \<kappa> (D, Cw, Fw, Rw) G c g d" using GM by simp
  have Res2: "\<forall> d. d \<notin> c` sentences \<longrightarrow> jump \<kappa> (D, Cw, Fw, Rw) G c f d \<le> jump \<kappa> (D, Cw, Fw, Rw) G c g d" by auto
  
  have "\<forall> d. jump \<kappa> (D, Cw, Fw, Rw) G c f d \<le> jump \<kappa> (D, Cw, Fw, Rw) G c g d"
    using Res1 Res2 by smt
  then show "jump \<kappa> (D, Cw, Fw, Rw) G c f \<le> jump \<kappa> (D, Cw, Fw, Rw) G c g"
    using le_funI by blast
qed

lemma jump_\<nu>_monot: \<open> ground_mod f4 t4 (D, Cw, Fw, Rw) G c  \<Longrightarrow> f \<le> g
  \<Longrightarrow> jump \<nu> (D, Cw, Fw, Rw) G c f \<le> jump \<nu> (D, Cw, Fw, Rw) G c g\<close>
proof-
  assume GM: "ground_mod f4 t4 (D, Cw, Fw, Rw) G c"
  then have S: "c` sentences \<subseteq> D" by simp
  assume H: "f \<le> g"
  hence "Rw (G := (\<lambda> val_list. f (hd val_list)) )
       \<le> Rw (G := (\<lambda> val_list. g (hd val_list)) )"
    by (simp add: le_funD le_funI)

  then have "leqMod (modplus (D, Cw, Fw, Rw) G f) (modplus (D, Cw, Fw, Rw) G g)"
    by simp
  from this monot_in_\<nu> have Res: "\<And> s A.
    value_fm \<nu> s (modplus (D, Cw, Fw, Rw) G f) A
  \<le> value_fm \<nu> s (modplus (D, Cw, Fw, Rw) G g) A" by fastforce

  have "\<forall> A \<in> sentences.
    jump \<nu> (D, Cw, Fw, Rw) G c f (c A) \<le> jump \<nu> (D, Cw, Fw, Rw) G c g (c A)" proof
  fix A::"('c, 'b, 'd) fm"
  assume Asent: \<open>A \<in> sentences\<close>

  from S this have A: "jump \<nu> (D, Cw, Fw, Rw) G c f (c A) =
  value_fm \<nu> (\<lambda> x. undefined) (modplus (D, Cw, Fw, Rw) G f) A" using GM by simp

  from S Asent have B: "jump \<nu> (D, Cw, Fw, Rw) G c g (c A) =
  value_fm \<nu> (\<lambda> x. undefined) (modplus (D, Cw, Fw, Rw) G g) A" using GM by simp

  show "jump \<nu> (D, Cw, Fw, Rw) G c f (c A) \<le> jump \<nu> (D, Cw, Fw, Rw) G c g (c A)"
    using A B Res by simp
  qed
  from this have Res1: "\<forall> d \<in> c` sentences.
    jump \<nu> (D, Cw, Fw, Rw) G c f d \<le> jump \<nu> (D, Cw, Fw, Rw) G c g d" using GM by simp
  have Res2: "\<forall> d. d \<notin> c` sentences \<longrightarrow> jump \<nu> (D, Cw, Fw, Rw) G c f d \<le> jump \<nu> (D, Cw, Fw, Rw) G c g d" by auto
  
  have "\<forall> d. jump \<nu> (D, Cw, Fw, Rw) G c f d \<le> jump \<nu> (D, Cw, Fw, Rw) G c g d"
    using Res1 Res2 by smt
  then show "jump \<nu> (D, Cw, Fw, Rw) G c f \<le> jump \<nu> (D, Cw, Fw, Rw) G c g"
    using le_funI by blast
qed

lemma \<mu>_fixed_point_prop:
\<open>ground_mod f3 t3 (D, Cw, Fw, Rw) G c \<Longrightarrow>
 ( \<exists> g. jump \<mu> (D, Cw, Fw, Rw) G c g = g )\<close>
proof-
  assume GM: "ground_mod f3 t3 (D, Cw, Fw, Rw) G c"
  then have H: "c` sentences \<subseteq> D" by simp
  let ?U = "( UNIV :: ('v \<Rightarrow> bool3) set)"
  have 1: "ccpo ?U"
    using function_space_ccpo_bool3 by simp

    have "\<forall> g1 g2.
   g1 \<le> g2 \<longrightarrow> jump \<mu> (D, Cw, Fw, Rw) G c g1
             \<le> jump \<mu> (D, Cw, Fw, Rw) G c g2"
      using jump_\<mu>_monot GM by metis
  then have 2: "monot (jump \<mu> (D, Cw, Fw, Rw) G c)" by simp
  from 1 2 VisserFixp have "ccpo ( FixPs ?U (jump \<mu> (D, Cw, Fw, Rw) G c))"
    by blast
  from this ccpo_least_element have "\<exists>g. g \<in> (FixPs ?U (jump \<mu> (D, Cw, Fw, Rw) G c))" by auto
  then obtain g where Hg: \<open>g \<in> (FixPs ?U (jump \<mu> (D, Cw, Fw, Rw) G c))\<close> by auto
  show "\<exists> g. jump \<mu> (D, Cw, Fw, Rw) G c g = g" proof
    show "jump \<mu> (D, Cw, Fw, Rw) G c g = g" using FixPs_def Hg by blast
  qed
qed

lemma \<kappa>_fixed_point_prop:
\<open>ground_mod f3 t3 (D, Cw, Fw, Rw) G c \<Longrightarrow>
 ( \<exists> g. jump \<kappa> (D, Cw, Fw, Rw) G c g = g )\<close>
proof-
  assume GM: "ground_mod f3 t3 (D, Cw, Fw, Rw) G c"
  then have H: "c` sentences \<subseteq> D" by simp
  let ?U = "( UNIV :: ('v \<Rightarrow> bool3) set)"
  have 1: "ccpo ?U"
    using function_space_ccpo_bool3 by simp

    have "\<forall> g1 g2.
   g1 \<le> g2 \<longrightarrow> jump \<kappa> (D, Cw, Fw, Rw) G c g1
             \<le> jump \<kappa> (D, Cw, Fw, Rw) G c g2"
      using jump_\<kappa>_monot GM by metis
  then have 2: "monot (jump \<kappa> (D, Cw, Fw, Rw) G c)" by simp
  from 1 2 VisserFixp have "ccpo ( FixPs ?U (jump \<kappa> (D, Cw, Fw, Rw) G c))"
    by blast
  from this ccpo_least_element have "\<exists>g. g \<in> (FixPs ?U (jump \<kappa> (D, Cw, Fw, Rw) G c))" by auto
  then obtain g where Hg: \<open>g \<in> (FixPs ?U (jump \<kappa> (D, Cw, Fw, Rw) G c))\<close> by auto
  show "\<exists> g. jump \<kappa> (D, Cw, Fw, Rw) G c g = g" proof
    show "jump \<kappa> (D, Cw, Fw, Rw) G c g = g" using FixPs_def Hg by blast
  qed
qed

lemma \<nu>_fixed_point_prop:
\<open>ground_mod f4 t4 (D, Cw, Fw, Rw) G c \<Longrightarrow>
 ( \<exists> g. jump \<nu> (D, Cw, Fw, Rw) G c g = g )\<close>
proof-
  assume GM: "ground_mod f4 t4 (D, Cw, Fw, Rw) G c"
  then have H: "c` sentences \<subseteq> D" by simp
  let ?U = "( UNIV :: ('v \<Rightarrow> bool4) set)"
  have 1: "ccpo ?U"
    using function_space_ccpo_bool4 by simp

    have "\<forall> g1 g2.
   g1 \<le> g2 \<longrightarrow> jump \<nu> (D, Cw, Fw, Rw) G c g1
             \<le> jump \<nu> (D, Cw, Fw, Rw) G c g2"
      using jump_\<nu>_monot GM by metis
  then have 2: "monot (jump \<nu> (D, Cw, Fw, Rw) G c)" by simp
  from 1 2 VisserFixp have "ccpo ( FixPs ?U (jump \<nu> (D, Cw, Fw, Rw) G c))"
    by blast
  from this ccpo_least_element have "\<exists>g. g \<in> (FixPs ?U (jump \<nu> (D, Cw, Fw, Rw) G c))" by auto
  then obtain g where Hg: \<open>g \<in> (FixPs ?U (jump \<nu> (D, Cw, Fw, Rw) G c))\<close> by auto
  show "\<exists> g. jump \<nu> (D, Cw, Fw, Rw) G c g = g" proof
    show "jump \<nu> (D, Cw, Fw, Rw) G c g = g" using FixPs_def Hg by blast
  qed
qed

section \<open>The Transfer Theorem\<close>
(*
datatype ('function_type, 'N) tmP
= Const 'N
| Fun 'function_type \<open>('function_type, 'N) tm list\<close>

datatype ('function_type, 'N) fmP
= RelG \<open>('function_type, 'N) tmP\<close>
| Equ \<open>('function_type, 'N) tmP\<close> \<open>('function_type, 'N) tmP\<close>
| Fal
| And \<open>('function_type, 'N) fmP\<close> \<open>('function_type, 'N) fmP\<close>
| Neg \<open>('function_type, 'N) fmP\<close>
*)

datatype ('N) fmP
= RelG \<open>'N\<close>
(* | Equ \<open>'N\<close> \<open>'N\<close> *)
| FalP
| AndP \<open>'N fmP\<close> \<open>'N fmP\<close>
| NegP \<open>'N fmP\<close>

fun liftfmP :: \<open>'c \<Rightarrow> ('N \<Rightarrow> 'b) \<Rightarrow> 'N fmP \<Rightarrow> ('a, 'b, 'c) fm\<close> where
"liftfmP G namec (RelG n) = Rel G [ Const (namec n) ]" |
"liftfmP G namec FalP = Fal" |
"liftfmP G namec (AndP fm1 fm2) = And (liftfmP G namec fm1) (liftfmP G namec fm2)" |
"liftfmP G namec (NegP fm) = Neg (liftfmP G namec fm)"

type_synonym ('N, 'mybool) Pmodel
   = \<open>('N \<Rightarrow> 'mybool)\<close>

type_synonym ('mybool) Pscheme
   = \<open>'mybool \<times> 'mybool \<times> ('mybool \<Rightarrow> 'mybool) \<times> ('mybool \<Rightarrow> 'mybool \<Rightarrow> 'mybool)\<close>

fun value_fmP :: \<open>('mybool) Pscheme \<Rightarrow> ('N, 'mybool) Pmodel \<Rightarrow> 'N fmP \<Rightarrow> 'mybool\<close> where
"value_fmP (myFalse, myTrue, myNot, myAnd) v FalP = myFalse" |
"value_fmP (myFalse, myTrue, myNot, myAnd) v (RelG a) = v a" |
(* "value_fm (myFalse, myTrue, myNot, myAnd, myUni) w (D, Cw, Fw, Rw) (Equ tm1 tm2) = ( if (value_tm w (Cw,Fw) tm1 = value_tm w (Cw,Fw) tm2) then myTrue else myFalse)" | *)
"value_fmP (myFalse, myTrue, myNot, myAnd) v (AndP fm1 fm2) = ( myAnd (value_fmP (myFalse, myTrue, myNot, myAnd) v fm1) (value_fmP (myFalse, myTrue, myNot, myAnd) v fm2))" |
"value_fmP (myFalse, myTrue, myNot, myAnd) v (NegP f) = (myNot (value_fmP (myFalse, myTrue, myNot, myAnd) v f))"

fun value_fmPc where
"( value_fmPc (myFalse, myTrue, myNot, myAnd, myUni) v fm)
  = ( value_fmP (myFalse, myTrue, myNot, myAnd) v fm)"

type_synonym 'N reference_list 
 = \<open>'N \<Rightarrow> 'N fmP\<close>

datatype toy_type = toy_typeA | toy_typeB

fun testR ::"(toy_type reference_list)" where
"testR toy_typeA = NegP ( RelG toy_typeA )" |
"testR toy_typeB = AndP ( NegP (RelG toy_typeA)) (RelG toy_typeB)"

fun toy_type_nn where "toy_type_nn (x :: toy_type) = n3"
fun toy_type_nt where "toy_type_nt toy_typeA = n3" | "toy_type_nt toy_typeB = t3"
fun toy_type_tn where "toy_type_tn toy_typeA = t3" | "toy_type_tn toy_typeB = n3"
fun toy_type_fn where "toy_type_fn toy_typeA = f3" | "toy_type_fn toy_typeB = n3"
fun toy_type_nf where "toy_type_nf toy_typeA = n3" | "toy_type_nf toy_typeB = f3"
fun toy_type_tt where "toy_type_tt (x :: toy_type) = t3"
fun toy_type_ff where "toy_type_ff (x :: toy_type) = f3"
fun toy_type_ft where "toy_type_ft toy_typeA = f3" | "toy_type_ft toy_typeB = t3"
fun toy_type_tf where "toy_type_tf toy_typeA = t3" | "toy_type_tf toy_typeB = f3"

lemma \<open>toy_type_nn \<le> (f :: toy_type \<Rightarrow> bool3)\<close>
  by (metis (full_types) bool3.exhaust insertI1 insert_commute le_funI leq3.simps(1) leq3.simps(4) less_eq_bool3_def order_example1B supRs_def toy_type_nn.elims)
lemma \<open>toy_type_nt \<le> toy_type_tt\<close>
  by (metis (full_types) le_funI leq3.simps(4) less_eq_bool3_def order_refl toy_type.exhaust toy_type_nt.simps(1) toy_type_nt.simps(2) toy_type_tt.elims)

fun jumpP :: \<open>'mybool Pscheme \<Rightarrow> 'N reference_list \<Rightarrow> ('N, 'mybool) Pmodel
  \<Rightarrow> ('N, 'mybool) Pmodel\<close>
  where
"jumpP (myFalse, myTrue, myNot, myAnd) R v =
 (\<lambda> a. value_fmP (myFalse, myTrue, myNot, myAnd) v (R a))"

lemma \<open>fixedp toy_type_nn (jumpP (f3, t3, \<kappa>_not, \<kappa>_and) testR)\<close>
proof-
  have \<open>\<forall> a. jumpP (f3, t3, \<kappa>_not, \<kappa>_and) testR toy_type_nn a = toy_type_nn a\<close>
  proof fix a show \<open>jumpP (f3, t3, \<kappa>_not, \<kappa>_and) testR toy_type_nn a = toy_type_nn a\<close>
      by(cases "a"; simp) qed
  then have "jumpP (f3, t3, \<kappa>_not, \<kappa>_and) testR
   toy_type_nn = toy_type_nn" by(simp add: ext)
  then show ?thesis by (simp add: fixedp_def)
qed

lemma \<open>fixedp toy_type_nf (jumpP (f3, t3, \<kappa>_not, \<kappa>_and) testR)\<close>
proof-
  have \<open>\<forall> a. jumpP (f3, t3, \<kappa>_not, \<kappa>_and) testR toy_type_nf a = toy_type_nf a\<close>
  proof fix a show \<open>jumpP (f3, t3, \<kappa>_not, \<kappa>_and) testR toy_type_nf a = toy_type_nf a\<close>
      by(cases "a"; simp) qed
  then have "jumpP (f3, t3, \<kappa>_not, \<kappa>_and) testR
   toy_type_nf = toy_type_nf" by(simp add: ext)
  then show ?thesis by (simp add: fixedp_def)
qed

fun is_neutral_name :: \<open>( 'v , 'a, 'b, 'c, 'mybool) model \<Rightarrow> 'v set \<Rightarrow> 'b \<Rightarrow> bool\<close>
  where
"is_neutral_name (D, Cw, Fw, Rw) X a = ( (Cw a) \<notin> X )"

fun is_neutral_Rsymb :: \<open>( 'v , 'a, 'b, 'c, 'mybool) model \<Rightarrow> 'v set \<Rightarrow> 'c \<Rightarrow> bool\<close>
  where
"is_neutral_Rsymb (D, Cw, Fw, Rw) X F = ( \<forall> val_list val_list'.
(\<forall> x \<in> set val_list. x \<in> X) \<and> (\<forall> y \<in> set val_list'. y \<in> X)
 \<longrightarrow> Rw F val_list = Rw F val_list' )"

fun is_neutral_Fsymb :: \<open>( 'v , 'a, 'b, 'c, 'mybool) model \<Rightarrow> 'v set \<Rightarrow> 'a \<Rightarrow> bool\<close>
  where
"is_neutral_Fsymb (D, Cw, Fw, Rw) X f = ( \<forall> val_list val_list'.
(\<forall> x \<in> set val_list. x \<in> X) \<and> (\<forall> y \<in> set val_list'. y \<in> X)
 \<longrightarrow> Fw f val_list = Fw f val_list' )"

fun is_quant_enrichment :: \<open>'mybool \<Rightarrow> 'mybool \<Rightarrow> ('v, 'a, 'b, 'c, 'mybool) model \<Rightarrow> 'c \<Rightarrow> (('a, 'b, 'c) fm \<Rightarrow> 'v) \<Rightarrow> ('N \<Rightarrow> 'b) \<Rightarrow> (('a, 'b, 'c) fm \<Rightarrow> 'b) \<Rightarrow> 'N reference_list \<Rightarrow> bool\<close>
  where
"is_quant_enrichment myFalse myTrue (D, Cw, Fw, Rw) G c Pnamec quotnamec R = ( 
( ground_mod myFalse myTrue (D, Cw, Fw, Rw) G c) \<and>
  ( inj Pnamec \<and> inj quotnamec) \<and>
  ( \<forall> A \<in> sentences. (Cw (quotnamec A)) = c A) \<and>
  ( \<forall> n:: 'N. Cw (Pnamec n) = c (liftfmP G Pnamec (R n)) ) \<and>
  ( \<forall> b:: 'b. (b \<notin> range Pnamec \<and> b \<notin> quotnamec ` sentences)
   \<longrightarrow> is_neutral_name (D, Cw, Fw, Rw) (c` sentences) b) \<and>
  (\<forall> a:: 'a. is_neutral_Fsymb (D, Cw, Fw, Rw) (c` sentences) a) \<and>
  (\<forall> c':: 'c. is_neutral_Rsymb (D, Cw, Fw, Rw) (c` sentences) c') )"

section \<open>Generalisations\<close>

lemma "(n4, n4) \<le> (b4, b4)"
  by (simp add: less_eq_bool4_def)

lemma product_ccpo: \<open>\<lbrakk> ccpo (A :: ('a :: order) set);
 ccpo (B :: ('b :: order) set) \<rbrakk>
 \<Longrightarrow> ccpo (A \<times> B)\<close>
proof-
  assume HA: "ccpo A"
  assume HB: "ccpo B"
  have "\<forall>X\<subseteq> (A \<times> B). consi X (A \<times> B) \<longrightarrow> (\<exists>b\<in> (A\<times> B). supRs b X (A\<times>B))" proof
    fix X
    show " X \<subseteq> A \<times> B \<longrightarrow> consi X (A \<times> B) \<longrightarrow> (\<exists>b\<in>A \<times> B. supRs b X (A \<times> B))" proof
      assume HX: "X \<subseteq> (A \<times> B)"
      show "consi X (A\<times>B) \<longrightarrow> (\<exists>b\<in> (A\<times> B). supRs b X (A\<times>B))" proof
        assume HC: "consi X (A\<times>B)"
        let ?X1 = "fst ` X"
        from HX HC have "?X1 \<subseteq> A" by auto
        from HC have "\<forall>c \<in> X. \<forall> d \<in> X. \<exists>b \<in> (A\<times>B). c \<le> b \<and> d \<le> b" by (simp add: consi_def)
        from this have "\<forall>x\<in> ?X1. \<forall>y\<in>?X1. \<exists>b\<in>A. x \<le> b \<and> y \<le> b" by fastforce
        from this have "consi ?X1 A" by(simp add: consi_def)
        from this HA have "\<exists> ba \<in> A. supRs ba ?X1 A" using ccpo_def
          using \<open>fst ` X \<subseteq> A\<close> by blast
        then obtain ba where "ba \<in> A" and "supRs ba ?X1 A" by auto

        let ?X2 = "snd ` X"
        from HX HC have "?X2 \<subseteq> B" by auto
        from HC have "\<forall>c \<in> X. \<forall> d \<in> X. \<exists>b \<in> (A\<times>B). c \<le> b \<and> d \<le> b" by (simp add: consi_def)
        from this have "\<forall>x\<in> ?X2. \<forall>y\<in>?X2. \<exists>b\<in>B. x \<le> b \<and> y \<le> b" by fastforce
        from this have "consi ?X2 B" by(simp add: consi_def)
        from this HB have "\<exists> bb \<in> B. supRs bb ?X2 B" using ccpo_def
          using \<open>snd ` X \<subseteq> B\<close> by blast
        then obtain bb where "bb \<in> B" and "supRs bb ?X2 B" by auto

        show "(\<exists>b\<in> (A\<times> B). supRs b X (A\<times>B))" proof
          have 1: "(ba, bb) \<in> A \<times> B" using \<open>ba \<in> A\<close> \<open>bb \<in> B\<close> by auto
          have 2: "(\<forall>y\<in>X. y \<le> (ba, bb))" using HX \<open>supRs bb ?X2 B\<close> \<open>supRs ba ?X1 A\<close>
            by (simp add: less_eq_prod_def supRs_def)
          have 3: "(\<forall>y\<in>A \<times> B. (\<forall>ya\<in>X. ya \<le> y) \<longrightarrow> (ba, bb) \<le> y)" using \<open>supRs bb ?X2 B\<close> \<open>supRs ba ?X1 A\<close>
            by (simp add: less_eq_prod_def supRs_def)
          show "supRs (ba,bb) X (A \<times> B)" using 1 2 3 by(simp add:supRs_def)
        next
          show "(ba, bb) \<in> A \<times> B" using \<open>ba \<in> A\<close> \<open>bb \<in> B\<close> by auto
        qed
      qed
    qed
  qed
  then show "ccpo (A \<times> B)" by(simp add: ccpo_def)
qed

type_synonym ('w, 'v, 'a, 'b, 'c, 'mybool) Wmodel
 = \<open> 'v set \<times> ('w \<Rightarrow> ('v, 'a,'b,'c) const_mod) \<times> ('w \<Rightarrow> ('v, 'a,'b,'c) func_mod)
    \<times> ('w \<Rightarrow> ('v, 'a,'b,'c, 'mybool) rela_mod)\<close>

fun ground_Wmod :: \<open>'mybool \<Rightarrow> 'mybool \<Rightarrow> ('w, 'v, 'a, 'b, 'c, 'mybool) Wmodel
   \<Rightarrow> 'c \<Rightarrow> (('a, 'b, 'c) fm \<Rightarrow> 'v) \<Rightarrow> bool\<close> where
"ground_Wmod myFalse myTrue (D, \<CC>w, \<FF>w, \<RR>w) G c =
 ( (inj c \<and> c` sentences \<subseteq> D) \<and>
 ( \<forall> w rsymb val_list. rsymb \<noteq> G\<longrightarrow> 
        \<RR>w w rsymb val_list \<in> {myTrue, myFalse}) )"

(*
fun ground_Wmod :: \<open>'mybool \<Rightarrow> 'mybool \<Rightarrow> ('w, 'v, 'a, 'b, 'c, 'mybool) Wmodel
   \<Rightarrow> 'c \<Rightarrow> (('a, 'b, 'c) fm \<Rightarrow> 'v) \<Rightarrow> bool\<close> where
"ground_Wmod myFalse myTrue (W, D, \<CC>w, \<FF>w, \<RR>w) G c =
 (\<forall> w \<in> W. ground_mod myFalse myTrue (D, (\<CC>w w), (\<FF>w w), (\<RR>w w) ) G c)"
*)

(*
lemma helperL_locdet: \<open>A \<in> sentences \<Longrightarrow>
value_fm (myFalse, myTrue, myNot, myAnd, myUni) (\<lambda> x. undefined) M A = 
value_fm (myFalse, myTrue, myNot, myAnd, myUni) w M A\<close>
  by (smt empty_iff mem_Collect_eq prod_cases4 value_fm_locdetS)
*)

function jumpW :: \<open>('v, 'mybool) scheme \<Rightarrow> ('w, 'v, 'a, 'b, 'c, 'mybool) Wmodel
  \<Rightarrow> 'c \<Rightarrow> (('a, 'b, 'c) fm \<Rightarrow> 'v) \<Rightarrow> ('w \<Rightarrow> 'v \<Rightarrow> 'mybool) \<Rightarrow> ('w \<Rightarrow> 'v \<Rightarrow> 'mybool)\<close>
  where
"jumpW (myFalse, myTrue, myNot, myAnd, myUni) (D, \<CC>w, \<FF>w, \<RR>w) G c g =
( if (ground_Wmod myFalse myTrue (D, \<CC>w, \<FF>w, \<RR>w) G c) then
 (\<lambda> w A. if (A \<in> c` sentences) then
value_fm (myFalse, myTrue, myNot, myAnd, myUni) (\<lambda> x. undefined)
  (D, \<CC>w w, \<FF>w w, (\<RR>w w) (G := (\<lambda> val_list. (g w) (hd val_list)))) (inv c A) 
else myFalse ) else undefined)"
  apply auto[1]
  by blast
termination by lexicographic_order

lemma jumpW_\<mu>_monot: \<open> ground_Wmod f3 t3 (D, \<CC>w, \<FF>w, \<RR>w) G c  \<Longrightarrow> f \<le> g
  \<Longrightarrow> jumpW \<mu> (D, \<CC>w, \<FF>w, \<RR>w) G c f \<le> jumpW \<mu> (D, \<CC>w, \<FF>w, \<RR>w) G c g\<close>
proof-
  assume GM: "ground_Wmod f3 t3 (D, \<CC>w, \<FF>w, \<RR>w) G c"
  then have S: "c` sentences \<subseteq> D" by simp
  assume H: "f \<le> g"
  hence "\<forall> w. (\<RR>w w) (G := (\<lambda> val_list. (f w) (hd val_list)) )
       \<le> (\<RR>w w) (G := (\<lambda> val_list. (g w) (hd val_list)) )"
    by (simp add: H le_funD le_funI)

  then have "\<forall> w. leqMod (D, \<CC>w w, \<FF>w w, (\<RR>w w) (G := (\<lambda> val_list. (f w) (hd val_list))))
  (D, \<CC>w w, \<FF>w w, (\<RR>w w) (G := (\<lambda> val_list. (g w) (hd val_list))))"
    by simp
  from this monot_in_\<mu> have Res: "\<And> s A w.
    value_fm \<mu> s (D, \<CC>w w, \<FF>w w, (\<RR>w w) (G := (\<lambda> val_list. (f w) (hd val_list)))) A
  \<le> value_fm \<mu> s (D, \<CC>w w, \<FF>w w, (\<RR>w w) (G := (\<lambda> val_list. (g w) (hd val_list)))) A" by fastforce

  have "\<forall> w. \<forall> A \<in> sentences.
    jumpW \<mu> (D, \<CC>w, \<FF>w, \<RR>w) G c f w (c A) \<le> jumpW \<mu> (D, \<CC>w, \<FF>w, \<RR>w) G c g w (c A)" proof
    fix w
    show "\<forall> A \<in> sentences.
    jumpW \<mu> (D, \<CC>w, \<FF>w, \<RR>w) G c f w (c A) \<le> jumpW \<mu> (D, \<CC>w, \<FF>w, \<RR>w) G c g w (c A)" proof
    fix A::"('d, 'c, 'e) fm"
  assume Asent: \<open>A \<in> sentences\<close>

  from S this have A: "jumpW \<mu> (D, \<CC>w, \<FF>w, \<RR>w) G c f w (c A) =
  value_fm \<mu> (\<lambda> x. undefined) (D, \<CC>w w, \<FF>w w, (\<RR>w w) (G := (\<lambda> val_list. (f w) (hd val_list)))) A" using GM by simp

  from S Asent have B: "jumpW \<mu> (D, \<CC>w, \<FF>w, \<RR>w) G c g w (c A) =
  value_fm \<mu> (\<lambda> x. undefined) (D, \<CC>w w, \<FF>w w, (\<RR>w w) (G := (\<lambda> val_list. (g w) (hd val_list)))) A" using GM by simp

  show "jumpW \<mu> (D, \<CC>w, \<FF>w, \<RR>w) G c f w (c A) \<le> jumpW \<mu> (D, \<CC>w, \<FF>w, \<RR>w) G c g w (c A)"
    using A B Res by simp
qed
qed
  from this have Res1: "\<forall> w. \<forall> d \<in> c` sentences.
    jumpW \<mu> (D, \<CC>w, \<FF>w, \<RR>w) G c f w d \<le> jumpW \<mu> (D, \<CC>w, \<FF>w, \<RR>w) G c g w d" using GM by simp

  have A: "\<forall>w d. d \<notin> c` sentences \<longrightarrow> jumpW \<mu> (D, \<CC>w, \<FF>w, \<RR>w) G c f w d = f3" using GM by simp
  have B: "\<forall>w d. d \<notin> c` sentences \<longrightarrow> jumpW \<mu> (D, \<CC>w, \<FF>w, \<RR>w) G c g w d = f3" using GM by simp
  from A B have Res2: "\<forall> w d. d \<notin> c` sentences \<longrightarrow> jumpW \<mu> (D, \<CC>w, \<FF>w, \<RR>w) G c f w d \<le> jumpW \<mu> (D, \<CC>w, \<FF>w, \<RR>w) G c g w d" by simp
  
  have "\<forall> w d. jumpW \<mu> (D, \<CC>w, \<FF>w, \<RR>w) G c f w d \<le> jumpW \<mu> (D, \<CC>w, \<FF>w, \<RR>w) G c g w d"
    using Res1 Res2 by smt
  then show "jumpW \<mu> (D, \<CC>w, \<FF>w, \<RR>w) G c f \<le> jumpW \<mu> (D, \<CC>w, \<FF>w, \<RR>w) G c g"
    using le_funI by smt
qed

lemma jumpW_\<kappa>_monot: \<open> ground_Wmod f3 t3 (D, \<CC>w, \<FF>w, \<RR>w) G c  \<Longrightarrow> f \<le> g
  \<Longrightarrow> jumpW \<kappa> (D, \<CC>w, \<FF>w, \<RR>w) G c f \<le> jumpW \<kappa> (D, \<CC>w, \<FF>w, \<RR>w) G c g\<close>
proof-
  assume GM: "ground_Wmod f3 t3 (D, \<CC>w, \<FF>w, \<RR>w) G c"
  then have S: "c` sentences \<subseteq> D" by simp
  assume H: "f \<le> g"
  hence "\<forall> w. (\<RR>w w) (G := (\<lambda> val_list. (f w) (hd val_list)) )
       \<le> (\<RR>w w) (G := (\<lambda> val_list. (g w) (hd val_list)) )"
    by (simp add: H le_funD le_funI)

  then have "\<forall> w. leqMod (D, \<CC>w w, \<FF>w w, (\<RR>w w) (G := (\<lambda> val_list. (f w) (hd val_list))))
  (D, \<CC>w w, \<FF>w w, (\<RR>w w) (G := (\<lambda> val_list. (g w) (hd val_list))))"
    by simp
  from this monot_in_\<kappa> have Res: "\<And> s A w.
    value_fm \<kappa> s (D, \<CC>w w, \<FF>w w, (\<RR>w w) (G := (\<lambda> val_list. (f w) (hd val_list)))) A
  \<le> value_fm \<kappa> s (D, \<CC>w w, \<FF>w w, (\<RR>w w) (G := (\<lambda> val_list. (g w) (hd val_list)))) A" by fastforce

  have "\<forall> w. \<forall> A \<in> sentences.
    jumpW \<kappa> (D, \<CC>w, \<FF>w, \<RR>w) G c f w (c A) \<le> jumpW \<kappa> (D, \<CC>w, \<FF>w, \<RR>w) G c g w (c A)" proof
    fix w
    show "\<forall> A \<in> sentences.
    jumpW \<kappa> (D, \<CC>w, \<FF>w, \<RR>w) G c f w (c A) \<le> jumpW \<kappa> (D, \<CC>w, \<FF>w, \<RR>w) G c g w (c A)" proof
    fix A::"('d, 'c, 'e) fm"
  assume Asent: \<open>A \<in> sentences\<close>

  from S this have A: "jumpW \<kappa> (D, \<CC>w, \<FF>w, \<RR>w) G c f w (c A) =
  value_fm \<kappa> (\<lambda> x. undefined) (D, \<CC>w w, \<FF>w w, (\<RR>w w) (G := (\<lambda> val_list. (f w) (hd val_list)))) A" using GM by simp

  from S Asent have B: "jumpW \<kappa> (D, \<CC>w, \<FF>w, \<RR>w) G c g w (c A) =
  value_fm \<kappa> (\<lambda> x. undefined) (D, \<CC>w w, \<FF>w w, (\<RR>w w) (G := (\<lambda> val_list. (g w) (hd val_list)))) A" using GM by simp

  show "jumpW \<kappa> (D, \<CC>w, \<FF>w, \<RR>w) G c f w (c A) \<le> jumpW \<kappa> (D, \<CC>w, \<FF>w, \<RR>w) G c g w (c A)"
    using A B Res by simp
qed
qed
  from this have Res1: "\<forall> w. \<forall> d \<in> c` sentences.
    jumpW \<kappa> (D, \<CC>w, \<FF>w, \<RR>w) G c f w d \<le> jumpW \<kappa> (D, \<CC>w, \<FF>w, \<RR>w) G c g w d" using GM by simp

  have A: "\<forall>w d. d \<notin> c` sentences \<longrightarrow> jumpW \<kappa> (D, \<CC>w, \<FF>w, \<RR>w) G c f w d = f3" using GM by simp
  have B: "\<forall>w d. d \<notin> c` sentences \<longrightarrow> jumpW \<kappa> (D, \<CC>w, \<FF>w, \<RR>w) G c g w d = f3" using GM by simp
  from A B have Res2: "\<forall> w d. d \<notin> c` sentences \<longrightarrow> jumpW \<kappa> (D, \<CC>w, \<FF>w, \<RR>w) G c f w d \<le> jumpW \<kappa> (D, \<CC>w, \<FF>w, \<RR>w) G c g w d" by simp
  
  have "\<forall> w d. jumpW \<kappa> (D, \<CC>w, \<FF>w, \<RR>w) G c f w d \<le> jumpW \<kappa> (D, \<CC>w, \<FF>w, \<RR>w) G c g w d"
    using Res1 Res2 by smt
  then show "jumpW \<kappa> (D, \<CC>w, \<FF>w, \<RR>w) G c f \<le> jumpW \<kappa> (D, \<CC>w, \<FF>w, \<RR>w) G c g"
    using le_funI by smt
qed

lemma jumpW_\<nu>_monot: \<open> ground_Wmod f4 t4 (D, \<CC>w, \<FF>w, \<RR>w) G c  \<Longrightarrow> f \<le> g
  \<Longrightarrow> jumpW \<nu> (D, \<CC>w, \<FF>w, \<RR>w) G c f \<le> jumpW \<nu> (D, \<CC>w, \<FF>w, \<RR>w) G c g\<close>
proof-
  assume GM: "ground_Wmod f4 t4 (D, \<CC>w, \<FF>w, \<RR>w) G c"
  then have S: "c` sentences \<subseteq> D" by simp
  assume H: "f \<le> g"
  hence "\<forall> w. (\<RR>w w) (G := (\<lambda> val_list. (f w) (hd val_list)) )
       \<le> (\<RR>w w) (G := (\<lambda> val_list. (g w) (hd val_list)) )"
    by (simp add: H le_funD le_funI)

  then have "\<forall> w. leqMod (D, \<CC>w w, \<FF>w w, (\<RR>w w) (G := (\<lambda> val_list. (f w) (hd val_list))))
  (D, \<CC>w w, \<FF>w w, (\<RR>w w) (G := (\<lambda> val_list. (g w) (hd val_list))))"
    by simp
  from this monot_in_\<nu> have Res: "\<And> s A w.
    value_fm \<nu> s (D, \<CC>w w, \<FF>w w, (\<RR>w w) (G := (\<lambda> val_list. (f w) (hd val_list)))) A
  \<le> value_fm \<nu> s (D, \<CC>w w, \<FF>w w, (\<RR>w w) (G := (\<lambda> val_list. (g w) (hd val_list)))) A" by fastforce

  have "\<forall> w. \<forall> A \<in> sentences.
    jumpW \<nu> (D, \<CC>w, \<FF>w, \<RR>w) G c f w (c A) \<le> jumpW \<nu> (D, \<CC>w, \<FF>w, \<RR>w) G c g w (c A)" proof
    fix w
    show "\<forall> A \<in> sentences.
    jumpW \<nu> (D, \<CC>w, \<FF>w, \<RR>w) G c f w (c A) \<le> jumpW \<nu> (D, \<CC>w, \<FF>w, \<RR>w) G c g w (c A)" proof
    fix A::"('d, 'c, 'e) fm"
  assume Asent: \<open>A \<in> sentences\<close>

  from S this have A: "jumpW \<nu> (D, \<CC>w, \<FF>w, \<RR>w) G c f w (c A) =
  value_fm \<nu> (\<lambda> x. undefined) (D, \<CC>w w, \<FF>w w, (\<RR>w w) (G := (\<lambda> val_list. (f w) (hd val_list)))) A" using GM by simp

  from S Asent have B: "jumpW \<nu> (D, \<CC>w, \<FF>w, \<RR>w) G c g w (c A) =
  value_fm \<nu> (\<lambda> x. undefined) (D, \<CC>w w, \<FF>w w, (\<RR>w w) (G := (\<lambda> val_list. (g w) (hd val_list)))) A" using GM by simp

  show "jumpW \<nu> (D, \<CC>w, \<FF>w, \<RR>w) G c f w (c A) \<le> jumpW \<nu> (D, \<CC>w, \<FF>w, \<RR>w) G c g w (c A)"
    using A B Res by simp
qed
qed
  from this have Res1: "\<forall> w. \<forall> d \<in> c` sentences.
    jumpW \<nu> (D, \<CC>w, \<FF>w, \<RR>w) G c f w d \<le> jumpW \<nu> (D, \<CC>w, \<FF>w, \<RR>w) G c g w d" using GM by simp

  have A: "\<forall>w d. d \<notin> c` sentences \<longrightarrow> jumpW \<nu> (D, \<CC>w, \<FF>w, \<RR>w) G c f w d = f4" using GM by simp
  have B: "\<forall>w d. d \<notin> c` sentences \<longrightarrow> jumpW \<nu> (D, \<CC>w, \<FF>w, \<RR>w) G c g w d = f4" using GM by simp
  from A B have Res2: "\<forall> w d. d \<notin> c` sentences \<longrightarrow> jumpW \<nu> (D, \<CC>w, \<FF>w, \<RR>w) G c f w d \<le> jumpW \<nu> (D, \<CC>w, \<FF>w, \<RR>w) G c g w d" by simp
  
  have "\<forall> w d. jumpW \<nu> (D, \<CC>w, \<FF>w, \<RR>w) G c f w d \<le> jumpW \<nu> (D, \<CC>w, \<FF>w, \<RR>w) G c g w d"
    using Res1 Res2 by smt
  then show "jumpW \<nu> (D, \<CC>w, \<FF>w, \<RR>w) G c f \<le> jumpW \<nu> (D, \<CC>w, \<FF>w, \<RR>w) G c g"
    using le_funI by smt
qed

lemma \<mu>_Wfixed_point_prop:
\<open>ground_Wmod f3 t3 (D, \<CC>w, \<FF>w, \<RR>w) G c \<Longrightarrow>
 ( \<exists> g. jumpW \<mu> (D, \<CC>w, \<FF>w, \<RR>w) G c g = g )\<close>
proof-
  assume GM: "ground_Wmod f3 t3 (D, \<CC>w, \<FF>w, \<RR>w) G c"
  then have H: "c` sentences \<subseteq> D" by simp
  let ?U = "( UNIV :: ('w \<Rightarrow> 'v \<Rightarrow> bool3) set)"
  have 1: "ccpo ?U"
    using function_space_ccpo_bool3 function_space_ccpo_full by auto

    have "\<forall> g1 g2.
   g1 \<le> g2 \<longrightarrow> jumpW \<mu> (D, \<CC>w, \<FF>w, \<RR>w) G c g1
             \<le> jumpW \<mu> (D, \<CC>w, \<FF>w, \<RR>w) G c g2"
      using jumpW_\<mu>_monot GM by metis
  then have 2: "monot (jumpW \<mu> (D, \<CC>w, \<FF>w, \<RR>w) G c)" by simp
  from 1 2 VisserFixp have "ccpo ( FixPs ?U (jumpW \<mu> (D, \<CC>w, \<FF>w, \<RR>w) G c))"
    by blast
  from this ccpo_least_element have "\<exists>g. g \<in> (FixPs ?U (jumpW \<mu> (D, \<CC>w, \<FF>w, \<RR>w) G c))" by auto
  then obtain g where Hg: \<open>g \<in> (FixPs ?U (jumpW \<mu> (D, \<CC>w, \<FF>w, \<RR>w) G c))\<close> by auto
  show "\<exists> g. jumpW \<mu> (D, \<CC>w, \<FF>w, \<RR>w) G c g = g" proof
    show "jumpW \<mu> (D, \<CC>w, \<FF>w, \<RR>w) G c g = g" using FixPs_def Hg by blast
  qed
qed

lemma \<kappa>_Wfixed_point_prop:
\<open>ground_Wmod f3 t3 (D, \<CC>w, \<FF>w, \<RR>w) G c \<Longrightarrow>
 ( \<exists> g. jumpW \<kappa> (D, \<CC>w, \<FF>w, \<RR>w) G c g = g )\<close>
proof-
  assume GM: "ground_Wmod f3 t3 (D, \<CC>w, \<FF>w, \<RR>w) G c"
  then have H: "c` sentences \<subseteq> D" by simp
  let ?U = "( UNIV :: ('w \<Rightarrow> 'v \<Rightarrow> bool3) set)"
  have 1: "ccpo ?U"
    using function_space_ccpo_bool3 function_space_ccpo_full by auto

    have "\<forall> g1 g2.
   g1 \<le> g2 \<longrightarrow> jumpW \<kappa> (D, \<CC>w, \<FF>w, \<RR>w) G c g1
             \<le> jumpW \<kappa> (D, \<CC>w, \<FF>w, \<RR>w) G c g2"
      using jumpW_\<kappa>_monot GM by metis
  then have 2: "monot (jumpW \<kappa> (D, \<CC>w, \<FF>w, \<RR>w) G c)" by simp
  from 1 2 VisserFixp have "ccpo ( FixPs ?U (jumpW \<kappa> (D, \<CC>w, \<FF>w, \<RR>w) G c))"
    by blast
  from this ccpo_least_element have "\<exists>g. g \<in> (FixPs ?U (jumpW \<kappa> (D, \<CC>w, \<FF>w, \<RR>w) G c))" by auto
  then obtain g where Hg: \<open>g \<in> (FixPs ?U (jumpW \<kappa> (D, \<CC>w, \<FF>w, \<RR>w) G c))\<close> by auto
  show "\<exists> g. jumpW \<kappa> (D, \<CC>w, \<FF>w, \<RR>w) G c g = g" proof
    show "jumpW \<kappa> (D, \<CC>w, \<FF>w, \<RR>w) G c g = g" using FixPs_def Hg by blast
  qed
qed

lemma \<nu>_Wfixed_point_prop:
\<open>ground_Wmod f4 t4 (D, \<CC>w, \<FF>w, \<RR>w) G c \<Longrightarrow>
 ( \<exists> g. jumpW \<nu> (D, \<CC>w, \<FF>w, \<RR>w) G c g = g )\<close>
proof-
  assume GM: "ground_Wmod f4 t4 (D, \<CC>w, \<FF>w, \<RR>w) G c"
  then have H: "c` sentences \<subseteq> D" by simp
  let ?U = "( UNIV :: ('w \<Rightarrow> 'v \<Rightarrow> bool4) set)"
  have 1: "ccpo ?U"
    using function_space_ccpo_bool4 function_space_ccpo_full by auto

    have "\<forall> g1 g2.
   g1 \<le> g2 \<longrightarrow> jumpW \<nu> (D, \<CC>w, \<FF>w, \<RR>w) G c g1
             \<le> jumpW \<nu> (D, \<CC>w, \<FF>w, \<RR>w) G c g2"
      using jumpW_\<nu>_monot GM by metis
  then have 2: "monot (jumpW \<nu> (D, \<CC>w, \<FF>w, \<RR>w) G c)" by simp
  from 1 2 VisserFixp have "ccpo ( FixPs ?U (jumpW \<nu> (D, \<CC>w, \<FF>w, \<RR>w) G c))"
    by blast
  from this ccpo_least_element have "\<exists>g. g \<in> (FixPs ?U (jumpW \<nu> (D, \<CC>w, \<FF>w, \<RR>w) G c))" by auto
  then obtain g where Hg: \<open>g \<in> (FixPs ?U (jumpW \<nu> (D, \<CC>w, \<FF>w, \<RR>w) G c))\<close> by auto
  show "\<exists> g. jumpW \<nu> (D, \<CC>w, \<FF>w, \<RR>w) G c g = g" proof
    show "jumpW \<nu> (D, \<CC>w, \<FF>w, \<RR>w) G c g = g" using FixPs_def Hg by blast
  qed
qed

type_synonym ('w, 'v, 'a, 'b, 'c, 'mybool) tpmodel
 = \<open> ('w \<Rightarrow> 'w set \<Rightarrow> real) \<times> 'v set \<times> ('w \<Rightarrow> ('v, 'a,'b,'c) const_mod) \<times> ('w \<Rightarrow> ('v, 'a,'b,'c) func_mod)
    \<times> ('w \<Rightarrow> ('v, 'a,'b,'c, 'mybool) rela_mod)\<close>

fun is_probmes:: \<open>('w \<Rightarrow> 'w set \<Rightarrow> real) \<Rightarrow> bool\<close> where
"(is_probmes m) = ( \<forall> w :: 'w. (m w UNIV = 1
 \<and> (\<forall> A :: 'w set. m w A \<ge> 0) \<and>
 (\<forall> A B :: 'w set. A \<inter> B = {} \<longrightarrow> m w A + m w B = m w (A \<union> B)) ) )"

lemma probmes_subset: " \<lbrakk> is_probmes m; A \<subseteq> B \<rbrakk> \<Longrightarrow> m w A \<le> m w B"
proof-
  assume H: "is_probmes m"
  assume SS: "A \<subseteq> B"
  then have 1: "B = A \<union> (B - A)" by blast
  have 2: "A \<inter> (B -A) = {}" by blast
  from H 1 2 have 3: "m w B = m w A + m w (B - A)" by simp
  from H have 4: "m w (B - A) \<ge> 0" by simp
  from 3 4 show ?thesis by simp
qed

fun ground_tpmod :: \<open>'mybool \<Rightarrow> 'mybool \<Rightarrow> ('w, 'v, 'a, 'b, 'c, 'mybool) tpmodel
   \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> (('a, 'b, 'c) fm \<Rightarrow> 'v) \<Rightarrow> (rat \<Rightarrow> 'v) \<Rightarrow> bool\<close> where
"ground_tpmod myFalse myTrue (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 =
 ( (inj c1 \<and> c1` sentences \<subseteq> D) \<and> (inj c2) \<and> is_probmes m \<and>
 ( \<forall> w rsymb val_list. rsymb \<notin> { G, H } \<longrightarrow> 
        \<RR>w w rsymb val_list \<in> {myTrue, myFalse}) )"

fun modpplus :: \<open>('w, 'v, 'a, 'b, 'c, 'mybool) tpmodel \<Rightarrow> 'c \<Rightarrow> 'c
\<Rightarrow> ('w \<Rightarrow> 'v \<Rightarrow> 'mybool) \<Rightarrow> ('w \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'mybool) \<Rightarrow> 'w \<Rightarrow> ('v, 'a, 'b, 'c, 'mybool) model\<close>
  where
"modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g h w =
(D, \<CC>w w, \<FF>w w, (\<RR>w w)
 (G := (\<lambda> val_list. (g w) (hd val_list)), H := (\<lambda> val_list. (h w) (hd val_list) (last val_list)) ) )"

fun pVal_\<kappa> :: "('w, 'v, 'a, 'b, 'c, bool3) tpmodel \<Rightarrow> 'c \<Rightarrow> 'c
\<Rightarrow> ('w \<Rightarrow> 'v \<Rightarrow> bool3) \<Rightarrow> ('w \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool3) \<Rightarrow> 'w \<Rightarrow> ('a, 'b, 'c) fm \<Rightarrow> rat \<Rightarrow> bool3" where
"pVal_\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H g h w \<phi> q =
(if (m w {w1 . value_fm \<kappa> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g h w1) \<phi> = t3} \<ge> real_of_rat q) then t3 else (
if (m w {w1. value_fm \<kappa> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g h w1) \<phi> = f3} > (1 - real_of_rat q) ) then f3 else n3 ) )"

lemma jumptp_\<kappa>_monot_helperT:
" ground_tpmod f3 t3 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2
  \<Longrightarrow> g1 \<le> g2 \<Longrightarrow> h1 \<le> h2
  \<Longrightarrow> value_fm \<kappa> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = t3
  \<Longrightarrow> value_fm \<kappa> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> = t3"
proof-
  assume H1: "(ground_tpmod f3 t3 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2)"
  from this have Hpm: "is_probmes m" by auto
  assume H2: "g1 \<le> g2"
  assume H3: "h1 \<le> h2"

    have "\<forall> w. (\<RR>w w)
 (G := (\<lambda> val_list. (g1 w) (hd val_list)), H := (\<lambda> val_list. (h1 w) (hd val_list) (last val_list)) )
       \<le> (\<RR>w w)
 (G := (\<lambda> val_list. (g2 w) (hd val_list)), H := (\<lambda> val_list. (h2 w) (hd val_list) (last val_list)) )"
      by (simp add: H1 H2 H3 le_funD le_funI)
    from this have "\<forall> w1. leqMod (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1)" by simp
    from this monot_in_\<kappa> have leq_fact: "\<forall> w1. value_fm \<kappa> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> \<le> value_fm \<kappa> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi>" by fastforce
    from leq_fact have Implfact: "\<forall> w1. value_fm \<kappa> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = t3 \<longrightarrow>
  value_fm \<kappa> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> = t3"
      by (smt bool3.exhaust leq3.simps(6) leq3.simps(7) less_eq_bool3_def)
    assume "value_fm \<kappa> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = t3"
    from this Implfact show "value_fm \<kappa> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> = t3" by simp
  qed

lemma jumptp_\<kappa>_monot_helperF:
" ground_tpmod f3 t3 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2
  \<Longrightarrow> g1 \<le> g2 \<Longrightarrow> h1 \<le> h2
  \<Longrightarrow> value_fm \<kappa> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = f3
  \<Longrightarrow> value_fm \<kappa> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> = f3"
proof-
  assume H1: "(ground_tpmod f3 t3 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2)"
  from this have Hpm: "is_probmes m" by auto
  assume H2: "g1 \<le> g2"
  assume H3: "h1 \<le> h2"

    have "\<forall> w. (\<RR>w w)
 (G := (\<lambda> val_list. (g1 w) (hd val_list)), H := (\<lambda> val_list. (h1 w) (hd val_list) (last val_list)) )
       \<le> (\<RR>w w)
 (G := (\<lambda> val_list. (g2 w) (hd val_list)), H := (\<lambda> val_list. (h2 w) (hd val_list) (last val_list)) )"
      by (simp add: H1 H2 H3 le_funD le_funI)
    from this have "\<forall> w1. leqMod (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1)" by simp
    from this monot_in_\<kappa> have leq_fact: "\<forall> w1. value_fm \<kappa> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> \<le> value_fm \<kappa> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi>" by fastforce
    from leq_fact have Implfact: "\<forall> w1. value_fm \<kappa> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = f3 \<longrightarrow>
  value_fm \<kappa> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> = f3"
      by (smt bool3.exhaust leq3.simps less_eq_bool3_def)
    assume "value_fm \<kappa> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = f3"
    from this Implfact show "value_fm \<kappa> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> = f3" by simp
  qed

lemma pVal_\<kappa>_monot: "\<lbrakk> (ground_tpmod f3 t3 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2); 
   g1 \<le> g2; h1 \<le> h2 \<rbrakk> \<Longrightarrow>
  pVal_\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w \<phi> q
  \<le> pVal_\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w \<phi> q"
proof-
  assume H1: "(ground_tpmod f3 t3 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2)"
  from this have Hpm: "is_probmes m" by auto
  assume H2: "g1 \<le> g2"
  assume H3: "h1 \<le> h2"

  show ?thesis proof(cases "pVal_\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w \<phi> q")
  case n3
  then show ?thesis by(simp add: less_eq_bool3_def)
next
  case t3
  then have Ht31: "pVal_\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w \<phi> q = t3" by auto
  from Ht31 have Estimate1: \<open>m w {w1 . value_fm \<kappa> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = t3} \<ge> real_of_rat q\<close>
    by (smt Collect_cong bool3.distinct(1) bool3.simps(6) pVal_\<kappa>.simps)
  from jumptp_\<kappa>_monot_helperT H1 H2 H3
   have Implfact: "\<forall> w1. value_fm \<kappa> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = t3 \<longrightarrow>
  value_fm \<kappa> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> = t3"
      by (smt bool3.exhaust leq3.simps(6) leq3.simps(7) less_eq_bool3_def)

    let ?Set1 = "{w1 . value_fm \<kappa> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = t3}"
    let ?Set2 = "{w1 . value_fm \<kappa> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> = t3}"
    from Implfact have "?Set1 \<subseteq> ?Set2" by auto
    from this Hpm probmes_subset[of "m" "?Set1" "?Set2"] have "m w ?Set1 \<le> m w ?Set2" by simp
    from this Estimate1 have "m w ?Set2 \<ge> real_of_rat q" by simp
    from this have Ht32: "pVal_\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w \<phi> q = t3" by simp
    from Ht31 Ht32 show ?thesis by simp
next
  case f3
    then have Hf31: "pVal_\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w \<phi> q = f3" by auto
  from Hf31 have Estimate2: \<open>m w {w1 . value_fm \<kappa> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = f3} > (1 - real_of_rat q)\<close>
    by (smt Collect_cong bool3.distinct bool3.simps pVal_\<kappa>.simps)
    from jumptp_\<kappa>_monot_helperF H1 H2 H3 have Implfact: "\<forall> w1. value_fm \<kappa> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = f3 \<longrightarrow>
  value_fm \<kappa> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> = f3"
      by (smt bool3.exhaust leq3.simps less_eq_bool3_def)

    let ?Set1 = "{w1 . value_fm \<kappa> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = f3}"
    let ?Set2 = "{w1 . value_fm \<kappa> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> = f3}"
    from Implfact have "?Set1 \<subseteq> ?Set2" by auto
    from this Hpm probmes_subset[of "m" "?Set1" "?Set2"] have "m w ?Set1 \<le> m w ?Set2" by simp
    from this Estimate2 have Cond1: "m w ?Set2 > 1 - real_of_rat q" by auto
    from this have Cond1B: "1 < real_of_rat q + m w ?Set2" by simp

let ?Set2T = "{w1 . value_fm \<kappa> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> = t3}"

  have "?Set2 \<union> ?Set2T \<subseteq> UNIV" by auto
  from this Hpm probmes_subset[of "m" "?Set2 \<union> ?Set2T" "UNIV"]
    have PS1: "m w (?Set2 \<union> ?Set2T) \<le> m w UNIV" by simp
  have "?Set2 \<inter> ?Set2T = {}" by auto
  from this Hpm have PS2: "m w ?Set2 + m w ?Set2T = m w (?Set2 \<union> ?Set2T)" by simp 
  from PS1 PS2 have PS3: "m w ?Set2 + m w ?Set2T \<le> m w UNIV" by simp
  have "m w UNIV = 1" using Hpm by simp
  from this PS3 have "m w ?Set2 + m w ?Set2T \<le> 1" by simp
  from this Cond1 have "m w ?Set2 + m w ?Set2T < real_of_rat q + m w ?Set2" by simp
  from this have Cond2: "m w ?Set2T < real_of_rat q" by simp
    from Cond1 Cond2 have Hf32: "pVal_\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w \<phi> q = f3" by simp
    from Hf31 Hf32 show ?thesis by simp
  qed
qed

fun pVal_\<mu> :: "('w, 'v, 'a, 'b, 'c, bool3) tpmodel \<Rightarrow> 'c \<Rightarrow> 'c
\<Rightarrow> ('w \<Rightarrow> 'v \<Rightarrow> bool3) \<Rightarrow> ('w \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool3) \<Rightarrow> 'w \<Rightarrow> ('a, 'b, 'c) fm \<Rightarrow> rat \<Rightarrow> bool3" where
"pVal_\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H g h w \<phi> q =
(if (m w {w1 . value_fm \<mu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g h w1) \<phi> = t3} \<ge> real_of_rat q
\<and> m w {w1 . value_fm \<mu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g h w1) \<phi> = n3} = 0) then t3 else (
if (m w {w1. value_fm \<mu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g h w1) \<phi> = f3} > (1 - real_of_rat q)
\<and> m w {w1 . value_fm \<mu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g h w1) \<phi> = n3} = 0) then f3 else n3 ) )"

lemma jumptp_\<mu>_monot_helperT:
" ground_tpmod f3 t3 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2
  \<Longrightarrow> g1 \<le> g2 \<Longrightarrow> h1 \<le> h2
  \<Longrightarrow> value_fm \<mu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = t3
  \<Longrightarrow> value_fm \<mu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> = t3"
proof-
  assume H1: "(ground_tpmod f3 t3 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2)"
  from this have Hpm: "is_probmes m" by auto
  assume H2: "g1 \<le> g2"
  assume H3: "h1 \<le> h2"

    have "\<forall> w. (\<RR>w w)
 (G := (\<lambda> val_list. (g1 w) (hd val_list)), H := (\<lambda> val_list. (h1 w) (hd val_list) (last val_list)) )
       \<le> (\<RR>w w)
 (G := (\<lambda> val_list. (g2 w) (hd val_list)), H := (\<lambda> val_list. (h2 w) (hd val_list) (last val_list)) )"
      by (simp add: H1 H2 H3 le_funD le_funI)
    from this have "\<forall> w1. leqMod (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1)" by simp
    from this monot_in_\<mu> have leq_fact: "\<forall> w1. value_fm \<mu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> \<le> value_fm \<mu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi>" by fastforce
    from leq_fact have Implfact: "\<forall> w1. value_fm \<mu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = t3 \<longrightarrow>
  value_fm \<mu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> = t3"
      by (smt bool3.exhaust leq3.simps(6) leq3.simps(7) less_eq_bool3_def)
    assume "value_fm \<mu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = t3"
    from this Implfact show "value_fm \<mu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> = t3" by simp
  qed

lemma jumptp_\<mu>_monot_helperF:
" ground_tpmod f3 t3 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2
  \<Longrightarrow> g1 \<le> g2 \<Longrightarrow> h1 \<le> h2
  \<Longrightarrow> value_fm \<mu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = f3
  \<Longrightarrow> value_fm \<mu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> = f3"
proof-
  assume H1: "(ground_tpmod f3 t3 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2)"
  from this have Hpm: "is_probmes m" by auto
  assume H2: "g1 \<le> g2"
  assume H3: "h1 \<le> h2"

    have "\<forall> w. (\<RR>w w)
 (G := (\<lambda> val_list. (g1 w) (hd val_list)), H := (\<lambda> val_list. (h1 w) (hd val_list) (last val_list)) )
       \<le> (\<RR>w w)
 (G := (\<lambda> val_list. (g2 w) (hd val_list)), H := (\<lambda> val_list. (h2 w) (hd val_list) (last val_list)) )"
      by (simp add: H1 H2 H3 le_funD le_funI)
    from this have "\<forall> w1. leqMod (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1)" by simp
    from this monot_in_\<mu> have leq_fact: "\<forall> w1. value_fm \<mu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> \<le> value_fm \<mu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi>" by fastforce
    from leq_fact have Implfact: "\<forall> w1. value_fm \<mu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = f3 \<longrightarrow>
  value_fm \<mu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> = f3"
      by (smt bool3.exhaust leq3.simps less_eq_bool3_def)
    assume "value_fm \<mu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = f3"
    from this Implfact show "value_fm \<mu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> = f3" by simp
  qed

lemma pVal_\<mu>_monot: "\<lbrakk> (ground_tpmod f3 t3 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2); 
   g1 \<le> g2; h1 \<le> h2 \<rbrakk> \<Longrightarrow>
  pVal_\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w \<phi> q
  \<le> pVal_\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w \<phi> q"
proof-
  assume H1: "(ground_tpmod f3 t3 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2)"
  from this have Hpm: "is_probmes m" by auto
  assume H2: "g1 \<le> g2"
  assume H3: "h1 \<le> h2"

  show ?thesis proof(cases "pVal_\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w \<phi> q")
case n3
  then show ?thesis by(simp add:less_eq_bool3_def)
next
  case t3
  from t3 have Estimate1: "m w {w1 . value_fm \<mu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = t3} \<ge> real_of_rat q" 
    by (smt Collect_cong bool3.distinct bool3.simps pVal_\<mu>.simps)

let ?NSet1 = "{w1 . value_fm \<mu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = n3}"
  let ?NSet2 = "{w1 . value_fm \<mu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> = n3}"

  from t3 have Estimate2: "m w ?NSet1 = 0"
    by (smt Collect_cong bool3.distinct bool3.simps pVal_\<mu>.simps)
  have "\<forall> w1.
value_fm \<mu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> = n3
\<longrightarrow> value_fm \<mu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = n3" proof
    fix w1
    show "value_fm \<mu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> = n3
\<longrightarrow> value_fm \<mu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = n3"
    proof(cases "value_fm \<mu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi>")
    case n3
      then show ?thesis by simp
      next
    case t3
      from this jumptp_\<mu>_monot_helperT H1 H2 H3 have \<open>value_fm \<mu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> = t3\<close> by metis
      then show ?thesis by simp
    next
      case f3
      from this jumptp_\<mu>_monot_helperF H1 H2 H3 have \<open>value_fm \<mu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> = f3\<close> by metis
      then show ?thesis by simp
    qed
  qed
  hence "?NSet2 \<subseteq> ?NSet1" by auto 
  from this Hpm probmes_subset[of "m" "?NSet2" "?NSet1"]
  have \<open>m w ?NSet2 \<le> m w ?NSet1\<close> by simp
  from this Estimate2 have A: "m w ?NSet2 \<le> 0" by simp
  from Hpm have B: "m w ?NSet2 \<ge> 0" by simp
  from A B have Estimate3: "m w ?NSet2 = 0" by simp

  from jumptp_\<mu>_monot_helperT H1 H2 H3
   have Implfact: "\<forall> w1. value_fm \<mu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = t3 \<longrightarrow>
  value_fm \<mu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> = t3"
      by (smt bool3.exhaust leq3.simps(6) leq3.simps(7) less_eq_bool3_def)

    let ?Set1 = "{w1 . value_fm \<mu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = t3}"
    let ?Set2 = "{w1 . value_fm \<mu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> = t3}"
    from Implfact have "?Set1 \<subseteq> ?Set2" by auto
    from this Hpm probmes_subset[of "m" "?Set1" "?Set2"] have "m w ?Set1 \<le> m w ?Set2" by simp
    from this Estimate1 have Estimate4: "m w ?Set2 \<ge> real_of_rat q" by simp
    from Estimate3 Estimate4 have \<open>pVal_\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w \<phi> q = t3\<close> by simp
  then show ?thesis using t3 by simp
next
  case f3
  then have Estimate2: \<open>m w {w1 . value_fm \<mu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = f3} > (1 - real_of_rat q)\<close>
    by (smt Collect_cong bool3.distinct bool3.simps pVal_\<mu>.simps)
    from jumptp_\<mu>_monot_helperF H1 H2 H3 have Implfact: "\<forall> w1. value_fm \<mu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = f3 \<longrightarrow>
  value_fm \<mu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> = f3"
      by (smt bool3.exhaust leq3.simps less_eq_bool3_def)

    let ?Set1 = "{w1 . value_fm \<mu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = f3}"
    let ?Set2 = "{w1 . value_fm \<mu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> = f3}"
    from Implfact have "?Set1 \<subseteq> ?Set2" by auto
    from this Hpm probmes_subset[of "m" "?Set1" "?Set2"] have "m w ?Set1 \<le> m w ?Set2" by simp
    from this Estimate2 have Cond1: "m w ?Set2 > 1 - real_of_rat q" by auto
    from this have Cond1B: "1 < real_of_rat q + m w ?Set2" by simp

    let ?Set2T = "{w1 . value_fm \<mu> (\<lambda> x. undefined)
  (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> = t3}"

  have "?Set2 \<union> ?Set2T \<subseteq> UNIV" by auto
  from this Hpm probmes_subset[of "m" "?Set2 \<union> ?Set2T" "UNIV"]
    have PS1: "m w (?Set2 \<union> ?Set2T) \<le> m w UNIV" by simp
  have "?Set2 \<inter> ?Set2T = {}" by auto
  from this Hpm have PS2: "m w ?Set2 + m w ?Set2T = m w (?Set2 \<union> ?Set2T)" by simp 
  from PS1 PS2 have PS3: "m w ?Set2 + m w ?Set2T \<le> m w UNIV" by simp
  have "m w UNIV = 1" using Hpm by simp
  from this PS3 have "m w ?Set2 + m w ?Set2T \<le> 1" by simp
  from this Cond1 have "m w ?Set2 + m w ?Set2T < real_of_rat q + m w ?Set2" by simp
  from this have Cond2: "m w ?Set2T < real_of_rat q" by simp

let ?NSet1 = "{w1 . value_fm \<mu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = n3}"
  let ?NSet2 = "{w1 . value_fm \<mu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> = n3}"

  from f3 have Estimate2: "m w ?NSet1 = 0"
    by (smt Collect_cong bool3.distinct bool3.simps pVal_\<mu>.simps)
  have "\<forall> w1.
value_fm \<mu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> = n3
\<longrightarrow> value_fm \<mu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = n3" proof
    fix w1
    show "value_fm \<mu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> = n3
\<longrightarrow> value_fm \<mu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = n3"
    proof(cases "value_fm \<mu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi>")
    case n3
      then show ?thesis by simp
      next
    case t3
      from this jumptp_\<mu>_monot_helperT H1 H2 H3 have \<open>value_fm \<mu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> = t3\<close> by metis
      then show ?thesis by simp
    next
      case f3
      from this jumptp_\<mu>_monot_helperF H1 H2 H3 have \<open>value_fm \<mu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> = f3\<close> by metis
      then show ?thesis by simp
    qed
  qed
  hence "?NSet2 \<subseteq> ?NSet1" by auto 
  from this Hpm probmes_subset[of "m" "?NSet2" "?NSet1"]
  have \<open>m w ?NSet2 \<le> m w ?NSet1\<close> by simp
  from this Estimate2 have A: "m w ?NSet2 \<le> 0" by simp
  from Hpm have B: "m w ?NSet2 \<ge> 0" by simp
  from A B have Estimate3: "m w ?NSet2 = 0" by simp

  from Estimate3 Cond1 Cond2 have \<open>pVal_\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w \<phi> q = f3\<close> by simp
  then show ?thesis using f3 by simp
qed
qed

fun pVal_\<nu> :: "('w, 'v, 'a, 'b, 'c, bool4) tpmodel \<Rightarrow> 'c \<Rightarrow> 'c
\<Rightarrow> ('w \<Rightarrow> 'v \<Rightarrow> bool4) \<Rightarrow> ('w \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool4) \<Rightarrow> 'w \<Rightarrow> ('a, 'b, 'c) fm \<Rightarrow> rat \<Rightarrow> bool4" where
"pVal_\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H g h w \<phi> q =
(if (m w {w1 . value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g h w1) \<phi> \<ge> t4} \<ge> real_of_rat q
\<and> m w {w1 . value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g h w1) \<phi> \<ge> f4} > (1 - real_of_rat q) ) then b4
 else (
if (m w {w1. value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g h w1) \<phi> \<ge> t4} \<ge> real_of_rat q) then t4
else ( if (m w {w1 . value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g h w1) \<phi> \<ge> f4} > (1 - real_of_rat q) ) then f4
 else n4 ) ))"

lemma jumptp_\<nu>_monot_helperB:
" ground_tpmod f4 t4 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2
  \<Longrightarrow> g1 \<le> g2 \<Longrightarrow> h1 \<le> h2
  \<Longrightarrow> value_fm \<nu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = b4
  \<Longrightarrow> value_fm \<nu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> = b4"
proof-
  assume H1: "(ground_tpmod f4 t4 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2)"
  from this have Hpm: "is_probmes m" by auto
  assume H2: "g1 \<le> g2"
  assume H3: "h1 \<le> h2"

    have "\<forall> w. (\<RR>w w)
 (G := (\<lambda> val_list. (g1 w) (hd val_list)), H := (\<lambda> val_list. (h1 w) (hd val_list) (last val_list)) )
       \<le> (\<RR>w w)
 (G := (\<lambda> val_list. (g2 w) (hd val_list)), H := (\<lambda> val_list. (h2 w) (hd val_list) (last val_list)) )"
      by (simp add: H1 H2 H3 le_funD le_funI)
    from this have "\<forall> w1. leqMod (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1)" by simp
    from this monot_in_\<nu> have leq_fact: "\<forall> w1. value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> \<le> value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi>" by fastforce
    from leq_fact have Implfact: "\<forall> w1. value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = b4 \<longrightarrow>
  value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> = b4"
      by (smt bool4.exhaust leq4.simps less_eq_bool4_def)
    assume "value_fm \<nu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = b4"
    from this Implfact show "value_fm \<nu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> = b4" by simp
  qed

lemma jumptp_\<nu>_monot_helperT:
" ground_tpmod f4 t4 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2
  \<Longrightarrow> g1 \<le> g2 \<Longrightarrow> h1 \<le> h2
  \<Longrightarrow> value_fm \<nu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = t4
  \<Longrightarrow> value_fm \<nu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> \<ge> t4"
proof-
  assume H1: "(ground_tpmod f4 t4 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2)"
  from this have Hpm: "is_probmes m" by auto
  assume H2: "g1 \<le> g2"
  assume H3: "h1 \<le> h2"

    have "\<forall> w. (\<RR>w w)
 (G := (\<lambda> val_list. (g1 w) (hd val_list)), H := (\<lambda> val_list. (h1 w) (hd val_list) (last val_list)) )
       \<le> (\<RR>w w)
 (G := (\<lambda> val_list. (g2 w) (hd val_list)), H := (\<lambda> val_list. (h2 w) (hd val_list) (last val_list)) )"
      by (simp add: H1 H2 H3 le_funD le_funI)
    from this have "\<forall> w1. leqMod (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1)" by simp
    from this monot_in_\<nu> have leq_fact: "\<forall> w1. value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> \<le> value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi>" by fastforce
    from leq_fact have Implfact: "\<forall> w1. value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = t4 \<longrightarrow>
  value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> \<ge> t4"
      by (smt)
    assume "value_fm \<nu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = t4"
    from this Implfact show "value_fm \<nu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> \<ge> t4" by simp
(*    from this show "value_fm \<nu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> \<in> {t4, b4}"
      by (smt bool4.exhaust insertCI leq4.simps(5) leq4.simps(7) less_eq_bool4_def) *)
  qed

lemma jumptp_\<nu>_monot_helperF:
" ground_tpmod f4 t4 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2
  \<Longrightarrow> g1 \<le> g2 \<Longrightarrow> h1 \<le> h2
  \<Longrightarrow> value_fm \<nu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = f4
  \<Longrightarrow> value_fm \<nu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> \<ge> f4"
proof-
  assume H1: "(ground_tpmod f4 t4 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2)"
  from this have Hpm: "is_probmes m" by auto
  assume H2: "g1 \<le> g2"
  assume H3: "h1 \<le> h2"

    have "\<forall> w. (\<RR>w w)
 (G := (\<lambda> val_list. (g1 w) (hd val_list)), H := (\<lambda> val_list. (h1 w) (hd val_list) (last val_list)) )
       \<le> (\<RR>w w)
 (G := (\<lambda> val_list. (g2 w) (hd val_list)), H := (\<lambda> val_list. (h2 w) (hd val_list) (last val_list)) )"
      by (simp add: H1 H2 H3 le_funD le_funI)
    from this have "\<forall> w1. leqMod (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1)" by simp
    from this monot_in_\<nu> have leq_fact: "\<forall> w1. value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> \<le> value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi>" by fastforce
    from leq_fact have Implfact: "\<forall> w1. value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = f4 \<longrightarrow>
  value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> \<ge> f4"
      by (smt)
    assume "value_fm \<nu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> = f4"
    from this Implfact show "value_fm \<nu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> \<ge> f4" by simp
(*    from this show "value_fm \<nu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> \<in> {f4, b4}"
      by (smt bool4.exhaust insertCI leq4.simps less_eq_bool4_def) *)
  qed

lemma pVal_\<nu>_monot: "\<lbrakk> (ground_tpmod f4 t4 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2); 
   g1 \<le> g2; h1 \<le> h2 \<rbrakk> \<Longrightarrow>
  pVal_\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w \<phi> q
  \<le> pVal_\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w \<phi> q"
proof-
  assume H1: "(ground_tpmod f4 t4 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2)"
  from this have Hpm: "is_probmes m" by auto
  assume H2: "g1 \<le> g2"
  assume H3: "h1 \<le> h2"

  show ?thesis proof(cases "pVal_\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w \<phi> q")
case n4
  then show ?thesis by(simp add:less_eq_bool4_def)
next
  case t4
  from t4 have Estimate1: "m w {w1 . value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> \<ge> t4} \<ge> real_of_rat q" 
    by (smt Collect_cong bool4.distinct bool4.simps pVal_\<nu>.simps)

  from jumptp_\<nu>_monot_helperT jumptp_\<nu>_monot_helperB H1 H2 H3
   have Implfact: "\<forall> w1. value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> \<ge> t4 \<longrightarrow>
  value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> \<ge> t4"
     by (smt bool4.exhaust leq4.simps less_eq_bool4_def)

    let ?Set1 = "{w1 . value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> \<ge> t4}"
    let ?Set2 = "{w1 . value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> \<ge> t4}"
    from Implfact have "?Set1 \<subseteq> ?Set2" by auto
    from this Hpm probmes_subset[of "m" "?Set1" "?Set2"] have "m w ?Set1 \<le> m w ?Set2" by simp
    from this Estimate1 have Estimate4: "m w ?Set2 \<ge> real_of_rat q" by simp
    from Estimate4 have \<open>pVal_\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w \<phi> q \<in> {t4, b4}\<close> by simp
    from this have \<open>pVal_\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w \<phi> q \<ge> t4\<close>
      by (smt bool4.distinct(1) bool4.simps(10) bool4.simps(12) bool4.simps(6) bool4.simps(8) insert_iff leq4.elims(3) less_eq_bool4_def singletonD)
  then show ?thesis using t4 by simp
next
  case f4
  then have Estimate2: \<open>m w {w1 . value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> \<ge> f4} > (1 - real_of_rat q)\<close>
    by (smt Collect_cong bool4.distinct bool4.simps pVal_\<nu>.simps)
  from jumptp_\<nu>_monot_helperF jumptp_\<nu>_monot_helperB
  H1 H2 H3 have Implfact: "\<forall> w1. value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> \<ge> f4 \<longrightarrow>
  value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> \<ge> f4"
     by (smt bool4.exhaust leq4.simps less_eq_bool4_def)

    let ?Set1 = "{w1 . value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> \<ge> f4}"
    let ?Set2 = "{w1 . value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> \<ge> f4}"
    from Implfact have "?Set1 \<subseteq> ?Set2" by auto
    from this Hpm probmes_subset[of "m" "?Set1" "?Set2"] have "m w ?Set1 \<le> m w ?Set2" by simp
    from this Estimate2 have Cond1: "m w ?Set2 > 1 - real_of_rat q" by auto
    from this have Cond1B: "1 < real_of_rat q + m w ?Set2" by simp

    then have \<open>m w {w1 . value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> \<ge> f4} > (1 - real_of_rat q)\<close> by simp
    from this have \<open>pVal_\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w \<phi> q \<in> {f4, b4}\<close> by simp
    from this have \<open>pVal_\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w \<phi> q \<ge> f4\<close>
      by (smt bool4.distinct(1) bool4.simps insert_iff leq4.elims(3) less_eq_bool4_def singletonD)
    from this f4 show ?thesis by simp
  next
    case b4
    then have Estimate1: "m w {w1 . value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> \<ge> t4} \<ge> real_of_rat q" 
    by (smt Collect_cong bool4.distinct bool4.simps pVal_\<nu>.simps)

  from jumptp_\<nu>_monot_helperT jumptp_\<nu>_monot_helperB H1 H2 H3
   have Implfact: "\<forall> w1. value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> \<ge> t4 \<longrightarrow>
  value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> \<ge> t4"
     by (smt bool4.exhaust leq4.simps less_eq_bool4_def)

    let ?Set1 = "{w1 . value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> \<ge> t4}"
    let ?Set2 = "{w1 . value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> \<ge> t4}"
    from Implfact have "?Set1 \<subseteq> ?Set2" by auto
    from this Hpm probmes_subset[of "m" "?Set1" "?Set2"] have "m w ?Set1 \<le> m w ?Set2" by simp
    from this Estimate1 have Estimate4: "m w ?Set2 \<ge> real_of_rat q" by simp
    from Estimate4 have \<open>pVal_\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w \<phi> q \<in> {t4, b4}\<close> by simp
    from this have GreqP1: \<open>pVal_\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w \<phi> q \<ge> t4\<close>
      by (smt bool4.distinct(1) bool4.simps(10) bool4.simps(12) bool4.simps(6) bool4.simps(8) insert_iff leq4.elims(3) less_eq_bool4_def singletonD)

    from b4 have Estimate2: \<open>m w {w1 . value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> \<ge> f4} > (1 - real_of_rat q)\<close>
    by (smt Collect_cong bool4.distinct bool4.simps pVal_\<nu>.simps)
  from jumptp_\<nu>_monot_helperF jumptp_\<nu>_monot_helperB
  H1 H2 H3 have Implfact: "\<forall> w1. value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> \<ge> f4 \<longrightarrow>
  value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> \<ge> f4"
     by (smt bool4.exhaust leq4.simps less_eq_bool4_def)

    let ?Set1 = "{w1 . value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w1) \<phi> \<ge> f4}"
    let ?Set2 = "{w1 . value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> \<ge> f4}"
    from Implfact have "?Set1 \<subseteq> ?Set2" by auto
    from this Hpm probmes_subset[of "m" "?Set1" "?Set2"] have "m w ?Set1 \<le> m w ?Set2" by simp
    from this Estimate2 have Cond1: "m w ?Set2 > 1 - real_of_rat q" by auto
    from this have Cond1B: "1 < real_of_rat q + m w ?Set2" by simp

    then have \<open>m w {w1 . value_fm \<nu> (\<lambda> x. undefined)
(modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w1) \<phi> \<ge> f4} > (1 - real_of_rat q)\<close> by simp
    from this have \<open>pVal_\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w \<phi> q \<in> {f4, b4}\<close> by simp
    from this have GreqP2: \<open>pVal_\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w \<phi> q \<ge> f4\<close>
      by (smt bool4.distinct(1) bool4.simps insert_iff leq4.elims(3) less_eq_bool4_def singletonD)
    from GreqP2 GreqP1 have \<open>pVal_\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w \<phi> q = b4\<close>
      by (smt bool4.exhaust leq4.simps(5) leq4.simps(7) leq4.simps(9) less_eq_bool4_def)
    then show ?thesis using b4 by simp
  qed
qed

function jumptp\<kappa> (*:: \<open>('v, 'mybool) scheme \<Rightarrow> ('w, 'v, 'a, 'b, 'c, 'mybool) Wmodel
  \<Rightarrow> 'c \<Rightarrow> (('a, 'b, 'c) fm \<Rightarrow> 'v) \<Rightarrow> ('w \<Rightarrow> 'v \<Rightarrow> 'mybool) \<Rightarrow> ('w \<Rightarrow> 'v \<Rightarrow> 'mybool)\<close> *)
  where
"jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g,h) =
( if (ground_tpmod f3 t3 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2) then
 ( (\<lambda> w A. if (A \<in> c1` sentences) then
 value_fm \<kappa> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g h w) (inv c1 A)
 else f3 ),
   (\<lambda> w v1 v2. if (v1 \<in> c1`sentences \<and> v2 \<in> range c2) then 
     pVal_\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H g h w (inv c1 v1) (inv c2 v2)
else f3 ) )
else undefined)"
  apply auto[1]
  by blast
termination by lexicographic_order

lemma jumptp_\<kappa>_monot: \<open> ground_tpmod f3 t3 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2
  \<Longrightarrow> g1 \<le> g2 \<Longrightarrow> h1 \<le> h2
  \<Longrightarrow> fst (jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) \<le> 
      fst (jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) \<close>
proof-
  assume GM: "ground_tpmod f3 t3 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2"
  then have S: "c1` sentences \<subseteq> D" by simp
  assume H1: "g1 \<le> g2"
  assume H2: "h1 \<le> h2"
  have "\<forall> w. (\<RR>w w)
 (G := (\<lambda> val_list. (g1 w) (hd val_list)), H := (\<lambda> val_list. (h1 w) (hd val_list) (last val_list)) )
       \<le> (\<RR>w w)
 (G := (\<lambda> val_list. (g2 w) (hd val_list)), H := (\<lambda> val_list. (h2 w) (hd val_list) (last val_list)) )"
    by (simp add: H1 H2 le_funD le_funI)

  then have "\<forall> w. leqMod (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w)"
    by simp
  from this monot_in_\<kappa> have Res: "\<And> s A w.
    value_fm \<kappa> s (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w) A
  \<le> value_fm \<kappa> s (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w) A" by fastforce

  have "\<forall> w. \<forall> A \<in> sentences.
    fst (jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) w (c1 A) \<le> 
   fst (jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) w (c1 A)" proof
    fix w
    show "\<forall> A \<in> sentences.
    fst (jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) w (c1 A) \<le> 
   fst (jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) w (c1 A)" proof
  fix A::"('d, 'c, 'e) fm"
  assume Asent: \<open>A \<in> sentences\<close>

  from S this have A: "fst (jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) w (c1 A) =
  value_fm \<kappa> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w) A" using GM by simp

  from S Asent have B: "fst (jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) w (c1 A) =
  value_fm \<kappa> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w) A" using GM by simp

  show "fst (jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) w (c1 A) \<le> 
   fst (jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) w (c1 A)"
    using A B Res by simp
qed
qed
  from this have Res1: "\<forall> w. \<forall> d \<in> c1` sentences.
    fst (jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) w d \<le> fst (jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) w d" using GM by simp

  have A: "\<forall> w d. d \<notin> c1` sentences \<longrightarrow> fst (jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) w d = f3" using GM by simp
  have B: "\<forall> w d. d \<notin> c1` sentences \<longrightarrow> fst (jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) w d = f3" using GM by simp
  from A B have Res2: "\<forall> w d. d \<notin> c1` sentences \<longrightarrow> fst (jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) w d \<le> fst (jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) w d" by simp
  
  have "\<forall> w d. fst (jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) w d \<le> fst (jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) w d"
    using Res1 Res2 by smt
  then show "fst (jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) \<le> fst (jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2))"
    using le_funI by smt
qed

lemma jumptp_\<kappa>_monot2: \<open> ground_tpmod f3 t3 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2
  \<Longrightarrow> g1 \<le> g2 \<Longrightarrow> h1 \<le> h2
  \<Longrightarrow> snd (jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) \<le> 
      snd (jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) \<close>
proof-
  assume GM: "ground_tpmod f3 t3 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2"
  assume H1: "g1 \<le> g2"
  assume H2: "h1 \<le> h2"

  from GM H1 H2 have 1: "\<forall> w v1 v2. v1 \<in> c1`sentences \<and> v2 \<in> range c2 \<longrightarrow>
   snd (jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) w v1 v2 \<le> 
      snd (jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) w v1 v2"
    using pVal_\<kappa>_monot by (smt jumptp\<kappa>.simps snd_conv)
  
  from GM have 2: "\<forall> w v1 v2. v1 \<notin> c1`sentences \<or> v2 \<notin> range c2 \<longrightarrow>
   snd (jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) w v1 v2 \<le> 
      snd (jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) w v1 v2" by simp
  from 1 2 show ?thesis using le_funI by smt
qed

lemma \<kappa>tp_fixed_point_prop:
\<open>ground_tpmod f3 t3 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 \<Longrightarrow>
 ( \<exists> g h. jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g,h) = (g,h) )\<close>
proof-
  assume GM: "ground_tpmod f3 t3 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2"
  then have H: "c1` sentences \<subseteq> D" by simp
  let ?U1 = "( UNIV :: ('w \<Rightarrow> 'v \<Rightarrow> bool3) set)"
  have 1: "ccpo ?U1"
    using function_space_ccpo_bool3 function_space_ccpo_full by auto

  let ?U2 = "( UNIV :: ('w \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool3) set)"
  have 2: "ccpo ?U2"
    using function_space_ccpo_bool3 function_space_ccpo_full by metis

  let ?U = "?U1 \<times> ?U2"
  from 1 2 have 3: "ccpo ?U" using product_ccpo by metis

    have "\<forall> g1 g2 h1 h2.
   g1 \<le> g2 \<longrightarrow> h1 \<le> h2 \<longrightarrow> jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)
             \<le> jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)"
      using jumptp_\<kappa>_monot jumptp_\<kappa>_monot2 GM by (metis less_eq_prod_def)
    then have 4: "monot (jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2)" by simp
    have 5: "(jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2) ` ?U \<subseteq> ?U" by simp
  from 3 4 5 VisserFixp have "ccpo ( FixPs ?U (jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2))"
    by blast
  from this ccpo_least_element have "\<exists>g h. (g,h) \<in> (FixPs ?U (jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2))" by fast
  then obtain g h where Hg: \<open>(g,h) \<in> (FixPs ?U (jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2))\<close> by auto
  show "\<exists> g h. (jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2) (g,h) = (g,h)" proof
    show "\<exists> h. (jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2) (g,h) = (g,h)" proof
    show "(jumptp\<kappa> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2) (g, h) = (g, h)" using FixPs_def Hg by blast
  qed
qed
qed

function jumptp\<mu> (*:: \<open>('v, 'mybool) scheme \<Rightarrow> ('w, 'v, 'a, 'b, 'c, 'mybool) Wmodel
  \<Rightarrow> 'c \<Rightarrow> (('a, 'b, 'c) fm \<Rightarrow> 'v) \<Rightarrow> ('w \<Rightarrow> 'v \<Rightarrow> 'mybool) \<Rightarrow> ('w \<Rightarrow> 'v \<Rightarrow> 'mybool)\<close> *)
  where
"jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g,h) =
( if (ground_tpmod f3 t3 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2) then
 ( (\<lambda> w A. if (A \<in> c1` sentences) then
 value_fm \<mu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g h w) (inv c1 A)
 else f3 ),
   (\<lambda> w v1 v2. if (v1 \<in> c1`sentences \<and> v2 \<in> range c2) then 
     pVal_\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H g h w (inv c1 v1) (inv c2 v2)
else f3 ) )
else undefined)"
  apply auto[1]
  by blast
termination by lexicographic_order

lemma jumptp_\<mu>_monot: \<open> ground_tpmod f3 t3 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2
  \<Longrightarrow> g1 \<le> g2 \<Longrightarrow> h1 \<le> h2
  \<Longrightarrow> fst (jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) \<le> 
      fst (jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) \<close>
proof-
  assume GM: "ground_tpmod f3 t3 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2"
  then have S: "c1` sentences \<subseteq> D" by simp
  assume H1: "g1 \<le> g2"
  assume H2: "h1 \<le> h2"
  have "\<forall> w. (\<RR>w w)
 (G := (\<lambda> val_list. (g1 w) (hd val_list)), H := (\<lambda> val_list. (h1 w) (hd val_list) (last val_list)) )
       \<le> (\<RR>w w)
 (G := (\<lambda> val_list. (g2 w) (hd val_list)), H := (\<lambda> val_list. (h2 w) (hd val_list) (last val_list)) )"
    by (simp add: H1 H2 le_funD le_funI)

  then have "\<forall> w. leqMod (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w)"
    by simp
  from this monot_in_\<mu> have Res: "\<And> s A w.
    value_fm \<mu> s (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w) A
  \<le> value_fm \<mu> s (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w) A" by fastforce

  have "\<forall> w. \<forall> A \<in> sentences.
    fst (jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) w (c1 A) \<le> 
   fst (jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) w (c1 A)" proof
    fix w
    show "\<forall> A \<in> sentences.
    fst (jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) w (c1 A) \<le> 
   fst (jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) w (c1 A)" proof
  fix A::"('d, 'c, 'e) fm"
  assume Asent: \<open>A \<in> sentences\<close>

  from S this have A: "fst (jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) w (c1 A) =
  value_fm \<mu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w) A" using GM by simp

  from S Asent have B: "fst (jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) w (c1 A) =
  value_fm \<mu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w) A" using GM by simp

  show "fst (jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) w (c1 A) \<le> 
   fst (jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) w (c1 A)"
    using A B Res by simp
qed
qed
  from this have Res1: "\<forall> w. \<forall> d \<in> c1` sentences.
    fst (jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) w d \<le> fst (jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) w d" using GM by simp

  have A: "\<forall> w d. d \<notin> c1` sentences \<longrightarrow> fst (jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) w d = f3" using GM by simp
  have B: "\<forall> w d. d \<notin> c1` sentences \<longrightarrow> fst (jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) w d = f3" using GM by simp
  from A B have Res2: "\<forall> w d. d \<notin> c1` sentences \<longrightarrow> fst (jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) w d \<le> fst (jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) w d" by simp
  
  have "\<forall> w d. fst (jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) w d \<le> fst (jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) w d"
    using Res1 Res2 by smt
  then show "fst (jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) \<le> fst (jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2))"
    using le_funI by smt
qed

lemma jumptp_\<mu>_monot2: \<open> ground_tpmod f3 t3 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2
  \<Longrightarrow> g1 \<le> g2 \<Longrightarrow> h1 \<le> h2
  \<Longrightarrow> snd (jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) \<le> 
      snd (jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) \<close>
proof-
  assume GM: "ground_tpmod f3 t3 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2"
  assume H1: "g1 \<le> g2"
  assume H2: "h1 \<le> h2"

  from GM H1 H2 have 1: "\<forall> w v1 v2. v1 \<in> c1`sentences \<and> v2 \<in> range c2 \<longrightarrow>
   snd (jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) w v1 v2 \<le> 
      snd (jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) w v1 v2"
    using pVal_\<mu>_monot by (smt jumptp\<mu>.simps snd_conv)
  
  from GM have 2: "\<forall> w v1 v2. v1 \<notin> c1`sentences \<or> v2 \<notin> range c2 \<longrightarrow>
   snd (jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) w v1 v2 \<le> 
      snd (jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) w v1 v2" by simp
  from 1 2 show ?thesis using le_funI by smt
qed

lemma \<mu>tp_fixed_point_prop:
\<open>ground_tpmod f3 t3 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 \<Longrightarrow>
 ( \<exists> g h. jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g,h) = (g,h) )\<close>
proof-
  assume GM: "ground_tpmod f3 t3 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2"
  then have H: "c1` sentences \<subseteq> D" by simp
  let ?U1 = "( UNIV :: ('w \<Rightarrow> 'v \<Rightarrow> bool3) set)"
  have 1: "ccpo ?U1"
    using function_space_ccpo_bool3 function_space_ccpo_full by auto

  let ?U2 = "( UNIV :: ('w \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool3) set)"
  have 2: "ccpo ?U2"
    using function_space_ccpo_bool3 function_space_ccpo_full by metis

  let ?U = "?U1 \<times> ?U2"
  from 1 2 have 3: "ccpo ?U" using product_ccpo by metis

    have "\<forall> g1 g2 h1 h2.
   g1 \<le> g2 \<longrightarrow> h1 \<le> h2 \<longrightarrow> jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)
             \<le> jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)"
      using jumptp_\<mu>_monot jumptp_\<mu>_monot2 GM by (metis less_eq_prod_def)
    then have 4: "monot (jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2)" by simp
    have 5: "(jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2) ` ?U \<subseteq> ?U" by simp
  from 3 4 5 VisserFixp have "ccpo ( FixPs ?U (jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2))"
    by blast
  from this ccpo_least_element have "\<exists>g h. (g,h) \<in> (FixPs ?U (jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2))" by fast
  then obtain g h where Hg: \<open>(g,h) \<in> (FixPs ?U (jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2))\<close> by auto
  show "\<exists> g h. (jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2) (g,h) = (g,h)" proof
    show "\<exists> h. (jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2) (g,h) = (g,h)" proof
    show "(jumptp\<mu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2) (g, h) = (g, h)" using FixPs_def Hg by blast
  qed
qed
qed

function jumptp\<nu> (*:: \<open>('v, 'mybool) scheme \<Rightarrow> ('w, 'v, 'a, 'b, 'c, 'mybool) Wmodel
  \<Rightarrow> 'c \<Rightarrow> (('a, 'b, 'c) fm \<Rightarrow> 'v) \<Rightarrow> ('w \<Rightarrow> 'v \<Rightarrow> 'mybool) \<Rightarrow> ('w \<Rightarrow> 'v \<Rightarrow> 'mybool)\<close> *)
  where
"jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g,h) =
( if (ground_tpmod f4 t4 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2) then
 ( (\<lambda> w A. if (A \<in> c1` sentences) then
 value_fm \<nu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g h w) (inv c1 A)
 else f4 ),
   (\<lambda> w v1 v2. if (v1 \<in> c1`sentences \<and> v2 \<in> range c2) then 
     pVal_\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H g h w (inv c1 v1) (inv c2 v2)
else f4 ) )
else undefined)"
  apply auto[1]
  by blast
termination by lexicographic_order

lemma jumptp_\<nu>_monot: \<open> ground_tpmod f4 t4 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2
  \<Longrightarrow> g1 \<le> g2 \<Longrightarrow> h1 \<le> h2
  \<Longrightarrow> fst (jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) \<le> 
      fst (jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) \<close>
proof-
  assume GM: "ground_tpmod f4 t4 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2"
  then have S: "c1` sentences \<subseteq> D" by simp
  assume H1: "g1 \<le> g2"
  assume H2: "h1 \<le> h2"
  have "\<forall> w. (\<RR>w w)
 (G := (\<lambda> val_list. (g1 w) (hd val_list)), H := (\<lambda> val_list. (h1 w) (hd val_list) (last val_list)) )
       \<le> (\<RR>w w)
 (G := (\<lambda> val_list. (g2 w) (hd val_list)), H := (\<lambda> val_list. (h2 w) (hd val_list) (last val_list)) )"
    by (simp add: H1 H2 le_funD le_funI)

  then have "\<forall> w. leqMod (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w)"
    by simp
  from this monot_in_\<nu> have Res: "\<And> s A w.
    value_fm \<nu> s (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w) A
  \<le> value_fm \<nu> s (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w) A" by fastforce

  have "\<forall> w. \<forall> A \<in> sentences.
    fst (jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) w (c1 A) \<le> 
   fst (jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) w (c1 A)" proof
    fix w
    show "\<forall> A \<in> sentences.
    fst (jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) w (c1 A) \<le> 
   fst (jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) w (c1 A)" proof
  fix A::"('d, 'c, 'e) fm"
  assume Asent: \<open>A \<in> sentences\<close>

  from S this have A: "fst (jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) w (c1 A) =
  value_fm \<nu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g1 h1 w) A" using GM by simp

  from S Asent have B: "fst (jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) w (c1 A) =
  value_fm \<nu> (\<lambda> x. undefined) (modpplus (m, D, \<CC>w, \<FF>w, \<RR>w) G H g2 h2 w) A" using GM by simp

  show "fst (jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) w (c1 A) \<le> 
   fst (jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) w (c1 A)"
    using A B Res by simp
qed
qed
  from this have Res1: "\<forall> w. \<forall> d \<in> c1` sentences.
    fst (jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) w d \<le> fst (jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) w d" using GM by simp

  have A: "\<forall> w d. d \<notin> c1` sentences \<longrightarrow> fst (jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) w d = f4" using GM by simp
  have B: "\<forall> w d. d \<notin> c1` sentences \<longrightarrow> fst (jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) w d = f4" using GM by simp
  from A B have Res2: "\<forall> w d. d \<notin> c1` sentences \<longrightarrow> fst (jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) w d \<le> fst (jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) w d" by simp
  
  have "\<forall> w d. fst (jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) w d \<le> fst (jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) w d"
    using Res1 Res2 by smt
  then show "fst (jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) \<le> fst (jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2))"
    using le_funI by smt
qed

lemma jumptp_\<nu>_monot2: \<open> ground_tpmod f4 t4 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2
  \<Longrightarrow> g1 \<le> g2 \<Longrightarrow> h1 \<le> h2
  \<Longrightarrow> snd (jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) \<le> 
      snd (jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) \<close>
proof-
  assume GM: "ground_tpmod f4 t4 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2"
  assume H1: "g1 \<le> g2"
  assume H2: "h1 \<le> h2"

  from GM H1 H2 have 1: "\<forall> w v1 v2. v1 \<in> c1`sentences \<and> v2 \<in> range c2 \<longrightarrow>
   snd (jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) w v1 v2 \<le> 
      snd (jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) w v1 v2"
    using pVal_\<nu>_monot by (smt jumptp\<nu>.simps snd_conv)
  
  from GM have 2: "\<forall> w v1 v2. v1 \<notin> c1`sentences \<or> v2 \<notin> range c2 \<longrightarrow>
   snd (jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)) w v1 v2 \<le> 
      snd (jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)) w v1 v2" by simp
  from 1 2 show ?thesis using le_funI by smt
qed

lemma \<nu>tp_fixed_point_prop:
\<open>ground_tpmod f4 t4 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 \<Longrightarrow>
 ( \<exists> g h. jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g,h) = (g,h) )\<close>
proof-
  assume GM: "ground_tpmod f4 t4 (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2"
  then have H: "c1` sentences \<subseteq> D" by simp
  let ?U1 = "( UNIV :: ('w \<Rightarrow> 'v \<Rightarrow> bool4) set)"
  have 1: "ccpo ?U1"
    using function_space_ccpo_bool4 function_space_ccpo_full by auto

  let ?U2 = "( UNIV :: ('w \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool4) set)"
  have 2: "ccpo ?U2"
    using function_space_ccpo_bool4 function_space_ccpo_full by metis

  let ?U = "?U1 \<times> ?U2"
  from 1 2 have 3: "ccpo ?U" using product_ccpo by metis

    have "\<forall> g1 g2 h1 h2.
   g1 \<le> g2 \<longrightarrow> h1 \<le> h2 \<longrightarrow> jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g1,h1)
             \<le> jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2 (g2,h2)"
      using jumptp_\<nu>_monot jumptp_\<nu>_monot2 GM by (metis less_eq_prod_def)
    then have 4: "monot (jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2)" by simp
    have 5: "(jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2) ` ?U \<subseteq> ?U" by simp
  from 3 4 5 VisserFixp have "ccpo ( FixPs ?U (jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2))"
    by blast
  from this ccpo_least_element have "\<exists>g h. (g,h) \<in> (FixPs ?U (jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2))" by fast
  then obtain g h where Hg: \<open>(g,h) \<in> (FixPs ?U (jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2))\<close> by auto
  show "\<exists> g h. (jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2) (g,h) = (g,h)" proof
    show "\<exists> h. (jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2) (g,h) = (g,h)" proof
    show "(jumptp\<nu> (m, D, \<CC>w, \<FF>w, \<RR>w) G H c1 c2) (g, h) = (g, h)" using FixPs_def Hg by blast
  qed
qed
qed

end
