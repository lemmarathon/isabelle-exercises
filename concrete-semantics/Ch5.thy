theory Ch5
imports Main "~~/src/Doc/Prog_Prove/Logic"
begin

(* 5.1 *)
lemma
  assumes T: "\<forall> x y. T x y \<or> T y x"
  and A: "\<forall> x y. A x y \<and> A y x \<longrightarrow> x = y"
  and TA: "\<forall> x y. T x y \<longrightarrow> A x y"
  and "A x y"
  shows "T x y"
proof -
  have "T x y \<or> T y x" using T by simp
  thus "?thesis"
  proof
    assume "T x y"
    thus "?thesis" by assumption
  next
    assume "T y x"
    hence "A y x" using TA by simp
    hence "A x y \<and> A y x" using \<open>A x y\<close> by simp
    hence "x = y" using A by simp
    thus "T x y" using \<open>T y x\<close> by simp
  qed
qed

(* 5.2 *)
lemma "\<exists>ys zs. xs = ys @ zs \<and> (length ys = length zs \<or> length ys = length zs + 1)"
proof -
  let ?n = "(length xs + 1) div 2"
  let ?ys = "take ?n xs"
  let ?zs = "drop ?n xs"
  have "xs = ?ys @ ?zs \<and> (length ?ys = length ?zs \<or> length ?ys = length ?zs + 1)" by auto
  thus "?thesis" by blast
qed

(* 5.3 *)
lemma assumes a: "ev (Suc(Suc n))" shows "ev n"
proof -
  show "?thesis" using a by cases
qed

(* 5.4 *)
lemma "\<not>ev (Suc (Suc (Suc 0)))" (is "\<not>?P")
proof
  assume "?P"
  hence "ev (Suc 0)" by cases
  thus "False" by cases
qed

(* 5.5 *)
inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  iter0: "iter r 0 x x" |
  iterS: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (S n) x z"

lemma "star r x y \<Longrightarrow> \<exists>n. iter r n x y"
proof (induction rule: star.induct)
  case (refl x)
  hence "iter r 0 x x" by (simp add: iter0)
  thus ?case by auto
next
  case (step x y z)
  then obtain n where "iter r n y z" by auto
  hence "iter r (Suc n) x z" using "step.hyps"(1) by (simp add: iterS)
  thus ?case by auto
qed

(* 5.6 *)
fun elems :: "'a list \<Rightarrow> 'a set" where
  "elems [] = {}" |
  "elems (x # xs) = {x} \<union> elems xs"

lemma "x \<in> elems xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys"
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case
  proof (cases "a = x")
    case True
    let ?ys = "[]"
    let ?zs = "xs"
    have "a # xs = ?ys @ x # ?zs \<and> x \<notin> elems ?ys" using True by auto
    thus ?thesis using True by blast
  next
    case False
    hence "x \<in> elems xs" using Cons.prems by auto
    then obtain ys zs where "xs = ys @ x # zs \<and> x \<notin> elems ys" using Cons.IH by auto
    hence "a # xs = (a # ys) @ x # zs \<and> x \<notin> elems (a # ys)" using False by auto
    thus ?thesis by blast
  qed
qed

(* 5.7 *)
datatype alpha = A | B

inductive S :: "alpha list \<Rightarrow> bool" where
  S_empty: "S []" |
  S_surround: "S w \<Longrightarrow> S (A # w @ [B])" |
  S_double: "S w1 \<Longrightarrow> S w2 \<Longrightarrow> S (w1 @ w2)"

inductive T :: "alpha list \<Rightarrow> bool" where
  T_empty: "T []" |
  T_step: "T w1 \<Longrightarrow> T w2 \<Longrightarrow> T (w1 @ [A] @ w2 @ [B])"

declare S.intros[simp,intro]

declare T.intros[simp,intro]

theorem T_S: "T w \<Longrightarrow> S w"
  by (simp add: T.inducts)

lemma T_app: "\<lbrakk> T w2 ; T w1 \<rbrakk> \<Longrightarrow> T (w1 @ w2)"
  apply(induction rule: T.induct)
  apply(simp)
  apply(metis T_step append_assoc)
done

theorem S_T: "S w \<Longrightarrow> T w"
  by(metis S.induct T.simps T_app append_Cons append_Nil)

theorem S_T_equiv: "S w = T w"
  by(metis T_S S_T)

fun balanced :: "nat \<Rightarrow> alpha list \<Rightarrow> bool" where
  "balanced 0 [] = True" |
  "balanced n (A # w) = balanced (Suc n) w" |
  "balanced (Suc n) (B # w) = balanced n w" |
  "balanced _ _ = False"

lemma balanced_nil: "balanced n [] \<Longrightarrow> n = 0"
  by (induction n, auto)

lemma balanced_cons: "balanced n (a # w) \<Longrightarrow>
    a = A \<and> balanced (Suc n) w \<or>
    a = B \<and> (\<exists> m. n = Suc m \<and> balanced m w)"
  using balanced.elims(2) by auto

lemma balanced_snoc: "balanced n w \<Longrightarrow> balanced (Suc n) (w @ [B])"
  by (induction n w rule: balanced.induct, auto)

lemma balanced_app: "balanced m v \<Longrightarrow> balanced n w \<Longrightarrow> balanced (m + n) (v @ w)"
  using balanced_cons by (induction v arbitrary: m, subst balanced_nil, auto, fastforce)

lemma replicate_cons_snoc: "replicate n a = a # as \<Longrightarrow> a # as = as @ [a]"
proof (induction as)
  case Nil
  then show ?case by (simp add: Cons_replicate_eq)
next
  case (Cons a as)
  then show ?case by (metis Cons_replicate_eq replicate_append_same)
qed

lemma T_replicate_Nil: "T (replicate n A) \<Longrightarrow> n = 0"
proof (induction "replicate n A" rule: T.induct)
  case T_empty
  then show ?case by auto
next
  case (T_step w1 w2)
  then show ?case
  proof (cases "replicate n A")
    case Nil
    then show ?thesis by auto
  next
    case (Cons a as)
    hence "a = A" by (metis Cons_replicate_eq)
    hence "replicate n A = as @ [A]" using Cons replicate_cons_snoc by fastforce
    hence "B = A" using T_step.hyps(5) by fastforce
    then show ?thesis by simp
  qed
qed

lemma S_replicate_Nil: "S (replicate n A) \<Longrightarrow> n = 0"
  using S_T_equiv T_replicate_Nil by blast

lemma S_balanced: "S (replicate n A @ w) \<Longrightarrow> balanced n w"
proof (induction "replicate n A @ w" arbitrary: n w rule: S.induct)
  case S_empty
  then show ?case by simp
next
  case (S_surround v)
  then show ?case
  proof (cases w)
    case Nil
    then show ?thesis
      using S.S_surround S_replicate_Nil S_surround.hyps(1) S_surround.hyps(3) by fastforce
  next
    let ?xs = "butlast w"
    let ?x = "last w"
    case (Cons a w')
    hence 0: "w = ?xs @ [?x]" by simp
    hence 1: "(A # v) @ [B] = (replicate n A @ ?xs) @ [?x]" using S_surround by simp
    hence 2: "B = ?x \<and> A # v = replicate n A @ ?xs" by simp
    then show ?thesis
    proof (cases n)
      case 0
      then show ?thesis
      proof (cases ?xs)
        case Nil
        then show ?thesis using 0 2 by simp
      next
        case (Cons x xs)
        hence 3: "A = x \<and> v = replicate 0 A @ xs" using 0 2 by simp
        hence 4: "balanced 0 xs" using S_surround by simp
        hence "w = A # xs @ [B]" using S_surround 0 3 by auto
        then show ?thesis using 0 4 balanced_snoc by force
      qed
    next
      case (Suc n')
      hence "v = replicate n' A @ ?xs" using 2 by simp
      hence "balanced n' ?xs" using S_surround by simp
      then show ?thesis using 0 balanced_snoc using 2 Suc by fastforce
    qed
  qed
next
  case (S_double w1 w2)
  hence "(\<exists>v. w1 = replicate n A @ v \<and> v @ w2 = w \<or> w1 @ v = replicate n A \<and> w2 = v @ w)"
    (is "\<exists>v. ?P v") by (simp add: append_eq_append_conv2)
  then obtain v where p: "?P v" by auto
  then show ?case
  proof
    assume 0: "w1 = replicate n A @ v \<and> v @ w2 = w"
    hence "balanced n v" using S_double by simp
    then show ?thesis
      by (metis S_double.hyps(4) 0 add.right_neutral append_Nil balanced_app replicate_0)
  next
    assume 1: "w1 @ v = replicate n A \<and> w2 = v @ w"
    then show ?thesis
    proof (cases n)
      case 0
      then show ?thesis using 1 S_double by simp
    next
      case (Suc n')
      hence "w1 @ v = replicate n' A @ [A]" using 1 by (simp add: replicate_append_same)
      then show ?thesis
        by (smt (verit, ccfv_threshold) 1 S_double.hyps S_replicate_Nil append_eq_append_conv
                length_0_conv length_append length_replicate replicate_add self_append_conv2)
    qed
  qed
qed

lemma S_app_in: "S (u @ w) \<Longrightarrow> S v \<Longrightarrow> S (u @ v @ w)"
proof (induction "u @ w" arbitrary: u w rule: S.induct)
  case S_empty
  then show ?case by simp
next
  case (S_surround v')
  then show ?case
  proof (cases w)
    case Nil
    hence "S u" using S.S_surround S_surround by auto
    then show ?thesis by (simp add: S_surround Nil)
  next
    case (Cons a w')
    let ?xs = "butlast w"
    let ?x = "last w"
    have 0: "w = ?xs @ [?x]" using Cons by simp
    hence 1: "(A # v') @ [B] = (u @ ?xs) @ [?x]" using S_surround by simp
    hence 2: "B = ?x \<and> A # v' = u @ ?xs" by simp
    then show ?thesis
    proof (cases u)
      case Nil
      hence 3: "A # v' = ?xs" using 2 by simp
      then show ?thesis
      proof (cases ?xs)
        case Nil
        then show ?thesis using \<open>A # v' = ?xs\<close> by simp
      next
        case (Cons x xs)
        hence 4: "A = x \<and> v' = xs" using 3 by simp
        hence "S (v @ xs)" using S_double S_surround by simp
        moreover have "v @ (x # xs) @ [?x] = v @ w" using 0 Nil S_surround Cons by simp
        hence "S w" using 2 4 S.S_surround S_surround by auto
        then show ?thesis using S_double S_surround Nil by simp
      qed
    next
      case (Cons b u')
      hence "A # v' = b # (u' @ ?xs)" using 2 by simp
      hence "A = b \<and> v' = u' @ ?xs" using 2 by simp
      hence "S (u' @ v @ ?xs)" using S_double S_surround by simp
      hence "S (A # (u' @ v @ ?xs) @ [B])" using S.S_surround by fastforce
      then show ?thesis using 0 2 Cons by auto
    qed
  qed
next
  case (S_double u' w')
  hence "\<exists>uw. u' = u @ uw \<and> uw @ w' = w \<or>
              u' @ uw = u \<and> w' = uw @ w" (is "\<exists>uw. ?P uw") by (simp add: append_eq_append_conv2)
  then obtain uw where p: "?P uw" by fastforce
  thus ?case
  proof
    assume "u' = u @ uw \<and> uw @ w' = w"
    hence "S (u @ v @ uw)" and "w = uw @ w'" using S_double.prems(1) S_double.hyps(2) by auto
    hence "S ((u @ v @ uw) @ w')" using S_double.hyps(3) S.S_double by blast
    thus ?thesis using \<open>w = uw @ w'\<close> by auto
  next
    assume "u' @ uw = u \<and> w' = uw @ w"
    hence "S (uw @ v @ w)" and "u = u' @ uw" using S_double.prems(1) S_double.hyps(4) by auto
    hence "S (u' @ uw @ v @ w)" using S_double.hyps(1) S.S_double by blast
    thus ?thesis using \<open>u = u' @ uw\<close> by auto
  qed
qed

lemma balanced_S: "balanced n w \<Longrightarrow> S (replicate n A @ w)"
proof (induction w arbitrary: n)
  case Nil
  hence "n = 0" by (cases n, auto)
  thus ?case by auto
next
  case (Cons a w)
  thus ?case
  proof (induction a arbitrary: n w)
    case A
    hence "balanced (Suc n) w" by simp
    hence "S (replicate (Suc n) A @ w)" using A.prems(1) by fastforce
    thus ?case using A by (simp add: replicate_app_Cons_same)
  next
    have "S [A, B]" using S.simps by blast
    case B
    hence "\<exists> m. n = Suc m \<and> balanced m w" using balanced_cons by fastforce
    then obtain m where p: "n = Suc m \<and> balanced m w" by fastforce
    hence "S (replicate m A @ w)" using B.prems(1) by simp
    hence "S (replicate m A @ [A, B] @ w)" using S_app_in \<open>S [A, B]\<close> by fastforce
    thus ?case by (simp add: p replicate_app_Cons_same)
  qed
qed

theorem balanced_S_equiv: "balanced n w = S (replicate n A @ w)" using S_balanced balanced_S by auto

end
