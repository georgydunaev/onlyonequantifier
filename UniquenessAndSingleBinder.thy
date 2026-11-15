theory UniquenessAndSingleBinder
  imports my_IFOL
begin

section \<open>Algebraic and Logical Laws of the Uniqueness Quantifier Only1 (!x. P(x))\<close>

text \<open>
  In my_IFOL.thy, unique existence (\<exists>!x. P(x)) is factored into standard existence
  (\<exists>x. P(x)) and the standalone uniqueness quantifier Only1 (!x. P(x)):
    !x. P(x) \<equiv> \<forall>x \<forall>y. P(x) \<and> P(y) \<longrightarrow> x = y
  Here we establish the fundamental structural laws of !x. P(x) and its dual
  ?x. P(x) \<equiv> \<not>(!x. \<not>P(x)) from yoneda.tex Section 1.2.
\<close>

subsection \<open>1. Vacuous Uniqueness, Singleton Uniqueness, and Downward Closure\<close>

lemma only1_vacuous:
  assumes H: \<open>\<forall>x. \<not> P(x)\<close>
  shows \<open>!x. P(x)\<close>
proof (rule only1I)
  fix x y
  assume px: \<open>P(x)\<close>
  from H have \<open>\<not> P(x)\<close> by (rule spec)
  from this px show \<open>x = y\<close> by (rule notE)
qed

lemma only1_singleton_eq: \<open>!x. x = a\<close>
proof (rule only1I)
  fix x y
  assume \<open>x = a\<close> and \<open>y = a\<close>
  then show \<open>x = y\<close> by (rule trans [OF _ sym])
qed

lemma only1_antimono:
  assumes sub: \<open>\<And>x. P(x) \<Longrightarrow> Q(x)\<close>
    and uQ: \<open>!x. Q(x)\<close>
  shows \<open>!x. P(x)\<close>
proof (rule only1I)
  fix x y
  assume \<open>P(x)\<close> and \<open>P(y)\<close>
  then have \<open>Q(x)\<close> and \<open>Q(y)\<close> by (rule sub)+
  with uQ show \<open>x = y\<close> by (rule only1D)
qed

lemma only1_conj_left:
  assumes uP: \<open>!x. P(x)\<close>
  shows \<open>!x. (P(x) \<and> Q(x))\<close>
proof (rule only1I)
  fix x y
  assume \<open>P(x) \<and> Q(x)\<close> and \<open>P(y) \<and> Q(y)\<close>
  then have \<open>P(x)\<close> and \<open>P(y)\<close> by (erule conjunct1)+
  with uP show \<open>x = y\<close> by (rule only1D)
qed

subsection \<open>2. Dual Quantifier from yoneda.tex Section 1.2\<close>

definition DualOnly1 :: \<open>('a \<Rightarrow> o) \<Rightarrow> o\<close>
  where dual_only1_def: \<open>DualOnly1(P) \<equiv> \<not> (!x. \<not> P(x))\<close>

lemma only1_dual_stable:
  assumes stable: \<open>\<And>x. \<not> \<not> P(x) \<Longrightarrow> P(x)\<close>
    and uP: \<open>!x. P(x)\<close>
  shows \<open>\<not> DualOnly1(\<lambda>x. \<not> P(x))\<close>
  unfold dual_only1_def
proof (rule notI)
  assume H: \<open>\<not> (!x. \<not> \<not> P(x))\<close>
  have uNNP: \<open>!x. \<not> \<not> P(x)\<close>
  proof (rule only1I)
    fix x y
    assume \<open>\<not> \<not> P(x)\<close> and \<open>\<not> \<not> P(y)\<close>
    then have \<open>P(x)\<close> and \<open>P(y)\<close> by (rule stable)+
    with uP show \<open>x = y\<close> by (rule only1D)
  qed
  from H uNNP show False by (rule notE)
qed

end
