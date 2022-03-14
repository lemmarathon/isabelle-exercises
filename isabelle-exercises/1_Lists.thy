theory "1_Lists"
imports Main
begin

(* https://isabelle.in.tum.de/exercises/ *)

(* 1.1 snoc *)
section snoc

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc [] a = [a]" | (* 0 *)
  "snoc (x # xs) a = x # snoc xs a" (* 1 + x *)

lemma snoc_app: "snoc xs x = xs @ [x]"
  by (induction xs, auto)

theorem rev_snoc: "rev (x # xs) = snoc (rev xs) x"
  by (simp add: snoc_app)

(* 1.2 replace *)
section replace

fun replace :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "replace x y [] = []" |
  "replace x y (z # zs) = (if z = x then y else z) # replace x y zs"

lemma replace_app_dist: "replace x y (zsl @ zsr) = replace x y zsl @ replace x y zsr"
  by (induction zsl; simp)

theorem "rev (replace x y zs) = replace x y (rev zs)"
  apply (induction zs, simp add: replace_app_dist)
  apply (auto simp add: replace_app_dist)
  done

theorem "replace x y (replace u v zs) = replace u v (replace x y zs)"
  oops

theorem "replace (0 :: nat) 1 (replace 1 0 [0]) \<noteq> replace 1 0 (replace 0 1 [0])"
  by simp

theorem "replace y z (replace x y zs) = replace x z zs"
  oops

theorem "replace (1 :: nat) 2 (replace 0 1 [1]) \<noteq> replace 0 2 [1]"
  by simp

fun del1 :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "del1 _ [] = []" |
  "del1 a (x # xs) = (if x = a then xs else x # del1 a xs)"

fun delall :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "delall _ [] = []" |
  "delall a (x # xs) = (if x = a then delall a xs else x # delall a xs)"

theorem [simp]: "del1 x (delall x xs) = delall x xs"
  by (induction xs; simp)

theorem "delall x (delall x xs) = delall x xs"
  by (induction xs; simp)

theorem "delall x (del1 x xs) = delall x xs"
  by (induction xs; simp)

theorem "del1 x (del1 y zs) = del1 y (del1 x zs)"
  by (induction zs; simp)

theorem "delall x (del1 y zs) = del1 y (delall x zs)"
  by (induction zs; simp)

theorem "delall x (delall y zs) = delall y (delall x zs)"
  by (induction zs; simp)

theorem "del1 y (replace x y xs) = del1 x xs"
  oops

theorem "del1 (1 :: nat) (replace 0 1 [1]) \<noteq> del1 0 [1]"
  by simp

theorem "delall y (replace x y xs) = delall x xs"
  oops

theorem "delall (1 :: nat) (replace 0 1 [1]) \<noteq> delall 0 [1]"
  by simp

theorem "replace x y (delall x zs) = delall x zs"
  by (induction zs; simp)

theorem "replace x y (delall z zs) = delall z (replace x y zs)"
  oops

theorem "replace (0 :: nat) 1 (delall 0 [0]) \<noteq> delall 0 (replace 0 1 [0])"
  by simp

theorem "rev(del1 x xs) = del1 x (rev xs)"
  oops

theorem "rev(del1 (0 :: nat) [0, 1, 0]) \<noteq> del1 0 (rev [0, 1, 0])"
  by simp

lemma [simp]: "delall x (xs @ ys) = delall x xs @ delall x ys"
  by (induction xs; simp)

theorem "rev(delall x xs) = delall x (rev xs)"
  by (induction xs; simp)

(* 1.3 quant *)
section quant



end
