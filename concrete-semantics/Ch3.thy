theory Ch3
imports Complex_Main "~~/src/HOL/IMP/AExp" "~~/src/HOL/IMP/BExp" "~~/src/HOL/IMP/ASM"
begin

(* 3.1 *)
fun optimal :: "aexp \<Rightarrow> bool" where
  "optimal (Plus (N _) (N _)) = False" |
  "optimal (Plus a1 a2) = (optimal a1 \<and> optimal a2)" |
  "optimal _ = True"

theorem optimal_asimp_const [simp]: "optimal (asimp_const a)"
  apply(induction a)
  apply(auto split: aexp.split)
done

(* 3.2 *)
fun zero_N :: "aexp \<Rightarrow> aexp" where
  "zero_N (N _) = (N 0)" |
  "zero_N (Plus a1 a2) = Plus (zero_N a1) (zero_N a2)" |
  "zero_N a = a"

fun full_sum :: "aexp \<Rightarrow> val" where
  "full_sum (N n) = n" |
  "full_sum (V v) = 0" | 
  "full_sum (Plus a1 a2) = full_sum a1 + full_sum a2"

fun expand_sum :: "aexp \<Rightarrow> aexp" where
  "expand_sum a = N (full_sum a)"

lemma plus_sum_zero_equiv [simp]: "aval (Plus (expand_sum a) (zero_N a)) s = aval a s"
  apply(induction a rule: zero_N.induct)
  apply(auto)
done

fun full_vars :: "aexp \<Rightarrow> vname list" where
  "full_vars (N n) = []" |
  "full_vars (V v) = [v]" |
  "full_vars (Plus a1 a2) = full_vars a1 @ full_vars a2"

fun expand_vlist :: "vname list \<Rightarrow> aexp" where
  "expand_vlist [v] = V v" |
  "expand_vlist (v # vs) = Plus (V v) (expand_vlist vs)" |
  "expand_vlist [] = N 0"

fun expand_vars :: "aexp \<Rightarrow> aexp" where
  "expand_vars a = expand_vlist (full_vars a)"

lemma vlist_cons [simp]: "aval (expand_vlist (v # vs)) s = aval (V v) s + aval (expand_vlist vs) s"
  apply(induction vs)
  apply(auto)
done

lemma vlist_app [simp]: "aval (expand_vlist (vs1 @ vs2)) s =
    aval (expand_vlist vs1) s + aval (expand_vlist vs2) s"
  apply(induction vs1)
  apply(auto)
done

lemma vars_zero_equiv [simp]: "aval (expand_vars a) s = aval (zero_N a) s"
  apply(induction a)
  apply(auto)
done

fun sum_vars :: "aexp \<Rightarrow> aexp" where
  "sum_vars a = Plus (expand_sum a) (expand_vars a)"

lemma sum_vars_correct [simp]: "aval (sum_vars a) s = aval a s"
  apply(induction a)
  apply(auto)
done

fun full_asimp :: "aexp \<Rightarrow> aexp" where
  "full_asimp a = asimp (sum_vars a)"

theorem full_asimp_correct: "aval (full_asimp a) s = aval a s"
  apply(induction a)
  apply(auto)
done

(* 3.3 *)
fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "subst x a (V v) = (if v = x then a else V v)" |
  "subst x a (Plus e1 e2) = Plus (subst x a e1) (subst x a e2)" |
  "subst x a e = e"

value "subst ''x'' (N 3) (Plus (V ''x'') (V ''y''))"

lemma subst_lemma [simp]: "aval (subst x a e) s = aval e (s(x := aval a s))"
  apply(induction e)
  apply(auto)
done

theorem subst_eq: "aval a1 s = aval a2 s \<Longrightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s"
  apply(induction e)
  apply(auto)
done

(* 3.4 *)
(* See Ch3_AExp.thy *)

(* 3.5 *)
datatype aexp2 = N2 val
               | V2 vname
               | Plus2 aexp2 aexp2
               | Times2 aexp2 aexp2
               | Div2 aexp2 aexp2
               | PostInc2 vname

fun aval2 :: "aexp2 \<Rightarrow> state \<Rightarrow> ((val, state) prod) option" where
  "aval2 (N2 n) s = Some (n, s)" |
  "aval2 (V2 v) s = Some (s v, s)" |
  "aval2 (Plus2 a1 a2) s = (
    case aval2 a1 s of Some (x, t) \<Rightarrow> (
      case aval2 a2 t of Some (y, u) \<Rightarrow> (
        Some (x + y, u)
      )
    )
  )" |
  "aval2 (Times2 a1 a2) s = (
    case aval2 a1 s of Some (x, t) \<Rightarrow> (
      case aval2 a2 t of Some (y, u) \<Rightarrow> (
        Some (x * y, u)
      )
    )
  )" |
  "aval2 (Div2 a1 a2) s = (
    case aval2 a1 s of Some (x, t) \<Rightarrow> (
      case aval2 a2 t of Some (y, u) \<Rightarrow> (
        if y = 0 then None else Some (x div y, u)
      )
    )
  )" |
  "aval2 (PostInc2 v) s = Some (s v, s(v := s v + 1))"
  
(* 3.6 *)

datatype lexp = Nl int | Vl vname | Plusl lexp lexp | LET vname lexp lexp

fun lval :: "lexp \<Rightarrow> state \<Rightarrow> int" where
  "lval (Nl n) s = n" |
  "lval (Vl v) s = s v" |
  "lval (Plusl e1 e2) s = lval e1 s + lval e2 s" |
  "lval (LET v e1 e2) s = lval e2 (s(v := lval e1 s))"

fun inline :: "lexp \<Rightarrow> aexp" where
  "inline (Nl n) = N n" |
  "inline (Vl v) = V v" |
  "inline (Plusl e1 e2) = Plus (inline e1) (inline e2)" |
  "inline (LET v e1 e2) = subst v (inline e1) (inline e2)"

theorem inline_correct: "lval e s = aval (inline e) s"
  apply(induction e arbitrary: s)
  apply(auto)
done

(* 3.7 *)
fun or :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
  "or (Bc True) _ = Bc True" |
  "or _ (Bc True) = Bc True" |
  "or (Bc False) b = b" |
  "or b (Bc False) = b" |
  "or b1 b2 = not(and (not(b1)) (not(b2)))"

fun Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "Eq (N n1) (N n2) = Bc (n1 = n2)" |
  "Eq a1 a2 = and (not(less a1 a2)) (not(less a2 a1))"

fun Le :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "Le (N n1) (N n2) = Bc (n1 \<le> n2)" |
  "Le a1 a2 = or (less a1 a2) (Eq a1 a2)"

theorem eq_correct [simp]: "bval (Eq a1 a2) s = (aval a1 s = aval a2 s)"
  apply(induction a1 rule: Eq.induct)
  apply(auto)
done

theorem le_correct [simp]: "bval (Le a1 a2) s = (aval a1 s \<le> aval a2 s)"
  apply(induction a1 rule: Le.induct)
  apply(auto)
done

(* 3.8 *)
datatype ifexp = Bc2 bool | If ifexp ifexp ifexp | Less2 aexp aexp

fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" where
  "ifval (Bc2 v) s = v" |
  "ifval (If bp bt be) s = (if (ifval bp s) then (ifval bt s) else (ifval be s))" |
  "ifval (Less2 a1 a2) s = (aval a1 s < aval a2 s)"

fun b2ifexp :: "bexp \<Rightarrow> ifexp" where
  "b2ifexp (Bc v) = Bc2 v" |
  "b2ifexp (Not b) = If (b2ifexp b) (Bc2 False) (Bc2 True)" |
  "b2ifexp (And b1 b2) = If (b2ifexp b1) (If (b2ifexp b2) (Bc2 True) (Bc2 False)) (Bc2 False)" |
  "b2ifexp (Less a1 a2) = Less2 a1 a2"

fun if2bexp :: "ifexp \<Rightarrow> bexp" where
  "if2bexp (Bc2 v) = Bc v" |
  "if2bexp (If bp bt be) = or (And (if2bexp bp) (if2bexp bt)) (And (Not (if2bexp bp)) (if2bexp be))" |
  "if2bexp (Less2 a1 a2) = Less a1 a2"

theorem b2ifexp_correct: "ifval (b2ifexp b) s = bval b s"
  apply(induction b)
  apply(auto)
done

theorem i2bfexp_correct: "bval (if2bexp i) s = ifval i s"
  apply(induction i)
  apply(auto)
done

(* 3.9 *)
datatype pbexp = VAR vname | NOT pbexp | AND pbexp pbexp | OR pbexp pbexp

fun pbval :: "pbexp \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> bool" where
  "pbval (VAR x) s = s x" |
  "pbval (NOT b) s = (\<not> pbval b s)" |
  "pbval (AND b1 b2) s = (pbval b1 s \<and> pbval b2 s)" |
  "pbval (OR b1 b2) s = (pbval b1 s \<or> pbval b2 s)"

fun is_nnf :: "pbexp \<Rightarrow> bool" where
  "is_nnf (VAR _) = True" |
  "is_nnf (NOT (VAR _)) = True" |
  "is_nnf (NOT _) = False" |
  "is_nnf (AND b1 b2) = (is_nnf b1 \<and> is_nnf b2)" |
  "is_nnf (OR b1 b2) = (is_nnf b1 \<and> is_nnf b2)"

fun nnf :: "pbexp \<Rightarrow> pbexp" where
  "nnf (NOT (NOT b)) = nnf b" |
  "nnf (NOT (AND b1 b2)) = OR (nnf (NOT b1)) (nnf (NOT b2))" |
  "nnf (NOT (OR b1 b2)) = AND (nnf (NOT b1)) (nnf (NOT b2))" |
  "nnf (AND b1 b2) = AND (nnf b1) (nnf b2)" |
  "nnf (OR b1 b2) = OR (nnf b1) (nnf b2)" |
  "nnf b = b"

theorem nnf_correct [simp]: "pbval (nnf b) s = pbval b s"
  apply(induction b rule: nnf.induct)
  apply(auto)
done

theorem nnf_is_nnf [simp]: "is_nnf (nnf b)"
  apply(induction b rule: nnf.induct)
  apply(auto)
done

fun no_or :: "pbexp \<Rightarrow> bool" where
  "no_or (AND b1 b2) = (no_or b1 \<and> no_or b2)" |
  "no_or (OR _ _) = False" |
  "no_or _ = True"

fun is_dnf :: "pbexp \<Rightarrow> bool" where
  "is_dnf (AND b1 b2) = (no_or b1 \<and> no_or b2)" |
  "is_dnf (OR b1 b2) = (is_dnf b1 \<and> is_dnf b2)" |
  "is_dnf _ = True" 

fun dist_AND :: "pbexp \<Rightarrow> pbexp \<Rightarrow> pbexp" where
  "dist_AND b (OR b1 b2) = OR (dist_AND b b1) (dist_AND b b2)" |
  "dist_AND (OR b1 b2) b = OR (dist_AND b1 b) (dist_AND b2 b)" |
  "dist_AND b1 b2 = AND b1 b2"

lemma dist_AND_correct [simp]: "pbval (dist_AND b1 b2) s = pbval (AND b1 b2) s"
  apply(induction b1 b2 rule: dist_AND.induct)
  apply(auto)
done

lemma is_dnf_dist [simp]: "is_dnf b1 \<Longrightarrow> is_dnf b2 \<Longrightarrow> is_dnf (dist_AND b1 b2)"
  apply(induction b1 b2 rule: dist_AND.induct)
  apply(auto)
done

fun dnf_of_nnf :: "pbexp \<Rightarrow> pbexp" where
  "dnf_of_nnf (AND b1 b2) = dist_AND (dnf_of_nnf b1) (dnf_of_nnf b2)" |
  "dnf_of_nnf (OR b1 b2) = OR (dnf_of_nnf b1) (dnf_of_nnf b2)" |
  "dnf_of_nnf b = b"

theorem dnf_of_nnf_correct [simp]: "pbval (dnf_of_nnf b) s = pbval b s"
  apply(induction b)
  apply(auto)
done

theorem dnf_of_nnf_converts: "is_nnf b \<Longrightarrow> is_dnf (dnf_of_nnf b)"
  apply(induction b rule: dnf_of_nnf.induct)
  apply(auto)
done

(* 3.10 *)
(* See Ch3_ASM.thy *)

(* 3.11 *)
type_synonym reg = nat

datatype instr = LDI val reg | LD vname reg | ADD reg reg

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
  "exec1 (LDI n r) _ rs = rs(r := n)" |
  "exec1 (LD v r) s rs = rs(r := s v)" |
  "exec1 (ADD r1 r2) _ rs = rs(r1 := rs r1 + rs r2)"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
  "exec [] _ rs = rs" |
  "exec (i # is) s rs = exec is s (exec1 i s rs)"

fun comp :: "aexp \<Rightarrow> reg \<Rightarrow> instr list" where
  "comp (N n) r = [LDI n r]" |
  "comp (V v) r = [LD v r]" |
  "comp (Plus e1 e2) r = comp e1 r @ comp e2 (r + 1) @ [ADD r (r + 1)]"

lemma exec_dist_app [simp]: "exec (is1 @ is2) s rs = exec is2 s (exec is1 s rs)"
  apply(induction is1 arbitrary: rs)
  apply(auto)
done

lemma exec_gt_r [simp]: "r2 > r1 \<Longrightarrow> exec (comp a r2) s rs r1 = rs r1"
  apply(induction a arbitrary: r1 r2 rs)
  apply(auto)
done

theorem comp_correct [simp]: "exec (comp a r) s rs r = aval a s"
  apply(induction a arbitrary: r rs)
  apply(auto)
done

(* 3.12 *)
datatype instr0 = LDI0 val | LD0 vname | MV0 reg | ADD0 reg

fun exec01 :: "instr0 \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
  "exec01 (LDI0 n) _ rs = rs(0 := n)" |
  "exec01 (LD0 v) s rs = rs(0 := s v)" |
  "exec01 (MV0 r) _ rs = rs(r := rs 0)" |
  "exec01 (ADD0 r) _ rs = rs(0 := rs 0 + rs r)"

fun exec0 :: "instr0 list \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
  "exec0 [] _ rs = rs" |
  "exec0 (i # is) s rs = exec0 is s (exec01 i s rs)"

fun comp0 :: "aexp \<Rightarrow> reg \<Rightarrow> instr0 list" where
  "comp0 (N n) r = [LDI0 n, MV0 r]" |
  "comp0 (V v) r = [LD0 v, MV0 r]" |
  "comp0 (Plus e1 e2) r =
    comp0 e1 (r + 1) @
    comp0 e2 (r + 2) @
    [LDI0 0, ADD0 (r + 1), ADD0 (r + 2), MV0 r]"

lemma exec0_dist_app [simp]: "exec0 (is1 @ is2) s rs = exec0 is2 s (exec0 is1 s rs)"
  apply(induction is1 arbitrary: rs)
  apply(auto)
done

lemma exec0_gt_r [simp]: "r2 > r1 \<Longrightarrow> r1 > 0 \<Longrightarrow> exec0 (comp0 a r2) s rs r1 = rs r1"
  apply(induction a arbitrary: r1 r2 rs)
  apply(auto)
done

theorem comp0_correct_r [simp]: "exec0 (comp0 a r) s rs r = aval a s"
  apply(induction a arbitrary: r rs)
  apply(auto)
done

theorem comp0_correct [simp]: "exec0 (comp0 a r) s rs 0 = aval a s"
  apply(induction a arbitrary: r rs)
  apply(auto)
done

end
