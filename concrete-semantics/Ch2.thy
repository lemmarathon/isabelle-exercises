theory Ch2
imports Complex_Main
begin

(* 2.1 *)
value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"

(* 2.2 *)
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

theorem add_assoc [simp]: "add a (add b c) = add (add a b) c"
  apply(induction a)
  apply(auto)
done

lemma add_n_0 [simp]: "add n 0 = n"
  apply(induction n)
  apply(auto)
done

lemma add_n_suc [simp]: "add n (Suc m) = Suc (add n m)"
  apply(induction n)
  apply(auto)
done

theorem add_comm [simp]: "add a b = add b a"
  apply(induction a)
  apply(auto)
done

fun double :: "nat \<Rightarrow> nat" where
  "double 0 = 0" |
  "double (Suc n) = Suc (Suc (double n))"

theorem double_add [simp]: "double n = n + n"
  apply(induction n)
  apply(auto)
done

(* 2.3 *)
fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count x [] = 0" |
  "count x (y # ys) = (if x = y then 1 else 0) + count x ys"

theorem count_lt_length [simp]: "count x xs \<le> length xs"
  apply(induction xs)
  apply(auto)
done

(* 2.4 *)
fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc [] x = [x]" |
  "snoc (y # ys) x = y # (snoc ys x)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse [] = []" |
  "reverse (x # xs) = snoc (reverse xs) x"

lemma reverse_snoc [simp]: "reverse (snoc xs a) = a # reverse xs"
  apply(induction xs)
  apply(auto)
done

theorem reverse_reverse [simp]: "reverse (reverse xs) = xs"
  apply(induction xs)
  apply(auto)
done

(* 2.5 *)
fun sum_upto :: "nat \<Rightarrow> nat" where
  "sum_upto 0 = 0" |
  "sum_upto n = n + sum_upto (n - 1)"

theorem sum_upto_nn1d2 [simp]: "sum_upto n = n * (n + 1) div 2"
  apply(induction n)
  apply(auto)
done

(* 2.6 *)
datatype 'a tree = Tip | Node  "'a tree"  'a  "'a tree"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
  "mirror Tip = Tip" |
  "mirror (Node l a r ) = Node (mirror r ) a (mirror l)"

fun contents :: "'a tree \<Rightarrow> 'a list" where
  "contents Tip = []" |
  "contents (Node l x r) = x # contents l @ contents r"

fun sum_tree :: "nat tree \<Rightarrow> nat" where
  "sum_tree Tip = 0" |
  "sum_tree (Node l x r) = x + sum_tree l + sum_tree r"

theorem sum_tree_sum_list_contents [simp]: "sum_tree t = sum_list (contents t)"
  apply(induction t)
  apply(auto)
done

(* 2.7 *)
fun pre_order :: "'a tree \<Rightarrow> 'a list" where
  "pre_order Tip = []" |
  "pre_order (Node l x r) = x # pre_order l @ pre_order r"

fun post_order :: "'a tree \<Rightarrow> 'a list" where
  "post_order Tip = []" |
  "post_order (Node l x r) = post_order l @ post_order r @ [x]"

theorem pre_order_rev_post_order [simp]: "pre_order (mirror t) = rev (post_order t)"
  apply(induction t)
  apply(auto)
done

(* 2.8 *)
fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intersperse a [] = []" |
  "intersperse a [x] = [x]" |
  "intersperse a (x1 # x2 # xs) = x1 # a # intersperse a (x2 # xs)"

theorem map_intersperse_intersperse_map [simp]:
    "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply(induction xs rule: intersperse.induct)
  apply(auto)
done

(* 2.9 *)
fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "itadd 0 n = n" |
  "itadd (Suc m) n = itadd m (Suc n)"

theorem itadd_add [simp]: "itadd m n = add m n"
  apply(induction m arbitrary: n)
  apply(auto)
done

(* 2.10 *)
datatype tree0 = Tip | Node tree0 tree0

fun nodes :: "tree0 \<Rightarrow> nat" where
  "nodes Tip = 1" |
  "nodes (Node l r) = 1 + nodes l + nodes r"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
  "explode 0 t = t" |
  "explode (Suc n) t = explode n (Node t t)"

theorem nodes_explode [simp]: "nodes (explode n t) = (nodes t + 1) * 2 ^ n - 1"
  apply(induction n arbitrary: t)
  apply(auto simp add: algebra_simps)
done

(* 2.11 *)
datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
  "eval Var v = v" |
  "eval (Const c) _ = c" |
  "eval (Add e1 e2) v = eval e1 v + eval e2 v" |
  "eval (Mult e1 e2) v = eval e1 v * eval e2 v"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "evalp [] v = 0" |
  "evalp (x # xs) v = x + v * evalp xs v"

fun addp :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "addp [] ys = ys" |
  "addp xs [] = xs" |
  "addp (x # xs) (y # ys) = (x + y) # addp xs ys"

fun mults :: "int \<Rightarrow> int list \<Rightarrow> int list" where
  "mults s [] = []" |
  "mults s (x # xs) = s * x # mults s xs"

fun multp :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "multp [] _ = []" |
  "multp _ [] = []" |
  "multp (x # xs) ys = addp (mults x ys) (0 # multp xs ys)"

fun coeffs :: "exp \<Rightarrow> int list" where
  "coeffs Var = [0, 1]" |
  "coeffs (Const c) = [c]" |
  "coeffs (Add e1 e2) = addp (coeffs e1) (coeffs e2)" |
  "coeffs (Mult e1 e2) = multp (coeffs e1) (coeffs e2)"

lemma evalp_addp [simp]: "evalp (addp xs ys) v = evalp xs v + evalp ys v"
  apply(induction xs ys rule: addp.induct)
  apply(auto simp add: algebra_simps)
done

lemma addp_nil [simp]: "addp xs [] = xs"
  apply(induction xs)
  apply(auto)
done

lemma multp_mults [simp]: "multp [x] ys = mults x ys"
  apply(induction ys)
  apply(auto simp add: algebra_simps)
done

lemma evalp_mults [simp]: "evalp (mults x ys) v = x * evalp ys v"
  apply(induction ys)
  apply(auto simp add: algebra_simps)
done

lemma evalp_multp_cons [simp]: "evalp (multp (x # xs) ys) v = x * evalp ys v + v * evalp (multp xs ys) v"
  apply(induction xs ys rule: multp.induct)
  apply(auto simp add: algebra_simps)
done

lemma evalp_multp [simp]: "evalp (multp xs ys) v = evalp xs v * evalp ys v"
  apply(induction xs arbitrary: ys)
  apply(auto simp add: algebra_simps)
done

theorem evalp_coeffs [simp]: "evalp (coeffs e) x = eval e x"
  apply(induction e rule: coeffs.induct)
  apply(auto simp add: algebra_simps)
done

end
