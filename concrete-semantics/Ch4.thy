theory Ch4
imports Main "~~/src/Doc/Prog_Prove/Logic" "~~/src/HOL/IMP/AExp"
begin

(* 4.1 *)
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun set :: "'a tree \<Rightarrow> 'a set" where
  "set Tip = {}" |
  "set (Node l x r) = {x} \<union> set l \<union> set r"

fun ord :: "int tree \<Rightarrow> bool" where
  "ord Tip = True" |
  "ord (Node l x r) = ((\<forall> y \<in> set l. y < x) \<and> (\<forall> y \<in> set r. x < y) \<and> ord l \<and> ord r)"

fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
  "ins x Tip = Node Tip x Tip" |
  "ins x (Node l x' r) = (
    if x < x' then (Node (ins x l) x' r)
    else (
      if x > x' then (Node l x' (ins x r))
      else (Node l x' r)
    )
  )"

theorem ins_set_correct [simp]: "set (ins x t) = {x} \<union> set t"
  apply(induction t)
  apply(auto)
done

theorem ins_ord_correct: "ord t \<Longrightarrow> ord (ins i t)"
  apply(induction t arbitrary: i)
  apply(auto)
done

(* 4.2 *)
inductive palindrome :: "'a list \<Rightarrow> bool" where
  palin_empty: "palindrome []" |
  palin_step: "palindrome xs \<Longrightarrow> palindrome (x # xs @ [x])"

theorem palin_rev: "palindrome xs \<Longrightarrow> rev xs = xs"
  apply(induction xs rule: palindrome.induct)
  apply(auto)
done

(* 4.3 *)
inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl': "star' r x x" |
  step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

lemma r_star: "r x y \<Longrightarrow> star r x y"
  by(blast intro: Logic.star.step Logic.star.refl)

theorem star'_star: "star' r x y \<Longrightarrow> star r x y"
  apply(induction rule: star'.induct)
  apply(rule Logic.star.refl)
  apply(rule Logic.star_trans)
  apply(assumption)
  apply(rule r_star)
  apply(assumption)
done

lemma r_star' [simp]: "r x y \<Longrightarrow> star' r x y"
  by(blast intro: refl' step')

lemma step'_r_star': "star' r y z \<Longrightarrow> r x y \<Longrightarrow> star' r x z"
  apply(induction rule: star'.induct)
  apply(simp_all add: step')
done

lemma star'_trans: "star' r x y \<Longrightarrow> star' r y z \<Longrightarrow> star' r x z"
  apply(induction rule: star'.induct)
  apply(simp)
  apply(metis step'_r_star')
done

theorem star_star': "star r x y \<Longrightarrow> star' r x y"
  apply(induction rule: star.induct)
  apply(simp_all add: refl')
  apply(metis step'_r_star')
done

(* 4.4 *)
inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  iter0: "iter r 0 x x" |
  iterS: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (S n) x z"

theorem star_iter: "star r x y \<Longrightarrow> \<exists>n. iter r n x y"
  apply(induction rule: star.induct)
  apply(metis iter0)
  apply(metis iterS)
done

(* 4.5 *)
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
  by(simp add: T.induct)

lemma T_app [simp]: "\<lbrakk> T w2 ; T w1 \<rbrakk> \<Longrightarrow> T (w1 @ w2)"
  apply(induction rule: T.induct)
  apply(simp)
  apply(metis T_step append_assoc)
done

theorem S_T: "S w \<Longrightarrow> T w"
  by (metis S.induct T.simps T_app append_Cons append_Nil)

theorem S_T_equiv: "S w = T w"
  by(metis T_S S_T)

(* 4.6 *)
inductive aval_rel :: "aexp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
  aval_rel_N: "aval_rel (N n) _ n" |
  aval_rel_V: "aval_rel (V v) s (s v)" |
  aval_rel_Plus: "aval_rel e1 s x \<Longrightarrow> aval_rel e2 s y \<Longrightarrow> aval_rel (Plus e1 e2) s (x + y)"

theorem aval_ind_rec: "aval_rel e s v \<Longrightarrow> aval e s = v"
  apply(induction rule: aval_rel.induct)
  apply(simp_all)
done

theorem aval_rec_ind: "aval e s = v \<Longrightarrow> aval_rel e s v"
  apply(induction e arbitrary: v)
  apply(auto simp add: aval_rel.intros)
done

theorem aval_rel_aval_equiv: "aval_rel e s v \<longleftrightarrow> aval e s = v"
  by(metis aval_ind_rec aval_rec_ind)

(* 4.7 *)
datatype instr = LOADI val | LOAD vname | ADD

type_synonym stack = "val list"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec1 (LOADI n) _ stk  =  n # stk" |
"exec1 (LOAD x) s stk  =  s(x) # stk" |
"exec1  ADD _ (j # i # stk)  =  (i + j) # stk"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec [] _ stk = stk" |
"exec (i#is) s stk = exec is s (exec1 i s stk)"

lemma exec_append[simp]:
  "exec (is1@is2) s stk = exec is2 s (exec is1 s stk)"
apply(induction is1 arbitrary: stk)
apply (auto split: option.split)
done

fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = [] @ [LOADI n]" |
"comp (V x) = [] @ [LOAD x]" |
"comp (Plus e\<^sub>1 e\<^sub>2) = comp e\<^sub>1 @ comp e\<^sub>2 @ [ADD]"

theorem exec_comp: "exec (comp a) s stk = aval a s # stk"
apply(induction a arbitrary: stk)
apply (auto)
done

inductive ok :: "nat \<Rightarrow> instr list \<Rightarrow> nat \<Rightarrow> bool" where
  ok_Nil: "ok n [] n" |
  ok_LOADI: "ok n is n' \<Longrightarrow> ok n (is @ [LOADI _]) (Suc n')" |
  ok_LOAD: "ok n is n' \<Longrightarrow> ok n (is @ [LOAD _]) (Suc n')" |
  ok_ADD: "ok n is (Suc (Suc n')) \<Longrightarrow> ok n (is @ [ADD]) (Suc n')"

declare ok.intros[simp,intro]

theorem ok_correct: "\<lbrakk>ok n is n'; length stk = n\<rbrakk> \<Longrightarrow> length (exec is s stk) = n'"
  apply(induction rule: ok.induct)
  apply(auto)
  apply(smt (verit, best) exec1.simps(3) length_Suc_conv)
done

lemma ok_append: "ok n' b n'' \<Longrightarrow> ok n a n' \<Longrightarrow> ok n (a @ b) n''"
  apply(induction rule: ok.induct)
  apply(simp)
  apply(metis append_assoc ok_LOADI)
  apply(metis append_assoc ok_LOAD)
  apply(metis append_assoc ok_ADD)
done

theorem "ok n (comp a) (Suc n)"
  apply(induction a arbitrary: n)
  apply(auto simp del: append_Nil)
  apply(auto intro: ok_append)
done

end
