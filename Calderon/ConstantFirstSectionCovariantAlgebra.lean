import Calderon.ActualPhysicalHalfFirstSectionGraphDictionary
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.ConstantFirstSectionCovariantAlgebra

theorem radius_smul_inclusion_inverse_add
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (I : V →L[ℝ] W) (r : ℝ) (hr : r ≠ 0) (a k : V) :
    r • I (r⁻¹ • a+k)=I a+r • I k := by
  simp only [map_add,map_smul,smul_add,smul_smul,mul_inv_cancel₀ hr,one_smul]

theorem radius_smul_covariant_split
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (I : V →L[ℝ] W) (r : ℝ) (hr : r ≠ 0)
    (a k : Fin 3 → V) (gamma : Fin 3 → ℝ) (xv xk : W) :
    r • (xv+xk-∑ l : Fin 3, gamma l • I (r⁻¹ • a l+k l)) =
      (r • xv-∑ l : Fin 3, gamma l • I (a l))+
      (r • xk-r • (∑ l : Fin 3, gamma l • I (k l))) := by
  have hSum : r • (∑ l : Fin 3, gamma l • I (r⁻¹ • a l+k l)) =
      (∑ l : Fin 3, gamma l • I (a l))+r • (∑ l : Fin 3, gamma l • I (k l)) := by
    have hTerms (l : Fin 3) : r • (gamma l • I (r⁻¹ • a l+k l)) =
        gamma l • I (a l)+r • (gamma l • I (k l)) := by
      have h := congrArg (fun v : W => gamma l • v) (radius_smul_inclusion_inverse_add I r hr (a l) (k l))
      exact (smul_comm r (gamma l) _).trans
        (h.trans ((smul_add (gamma l) (I (a l)) (r • I (k l))).trans
          (congrArg (fun v : W => gamma l • I (a l)+v) (smul_comm (gamma l) r _))))
    calc
      _ = ∑ l : Fin 3, r • (gamma l • I (r⁻¹ • a l+k l)) := by simp only [Finset.smul_sum]
      _ = ∑ l : Fin 3, (gamma l • I (a l)+r • (gamma l • I (k l))) :=
        Finset.sum_congr rfl (fun l _ => hTerms l)
      _ = _ := by simp only [Finset.sum_add_distrib,Finset.smul_sum]
  calc
    _ = r • xv+r • xk-r • (∑ l : Fin 3, gamma l • I (r⁻¹ • a l+k l)) := by simp only [smul_sub,smul_add]
    _ = r • xv+r • xk-((∑ l : Fin 3, gamma l • I (a l))+r • (∑ l : Fin 3, gamma l • I (k l))) :=
      congrArg (fun v : W => r • xv+r • xk-v) hSum
    _ = _ := by abel

theorem radius_smul_physical_sum
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (I : V →L[ℝ] W) (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ) (b : Fin 3 → ℝ)
    (c : Fin 3 → Fin 3 → W) (first : Fin 3 → V) :
    r • ((∑ i : Fin 3, ∑ j : Fin 3, Q i j • c i j)+(∑ i : Fin 3, b i • I (first i))) =
      (∑ i : Fin 3, ∑ j : Fin 3, Q i j • (r • c i j))+
      (∑ i : Fin 3, b i • (r • I (first i))) := by
  simp only [smul_add,Finset.smul_sum]
  exact congrArg₂ (fun x y : W => x+y)
    (Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => smul_comm r (Q i j) (c i j))))
    (Finset.sum_congr rfl (fun i _ => smul_comm r (b i) (I (first i))))

theorem principal_sum_split
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ) (D U : Fin 3 → Fin 3 → W) :
    (∑ i : Fin 3, ∑ j : Fin 3, Q i j • (r⁻¹ • D i j+U i j)) =
      r⁻¹ • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • D i j)+
      (∑ i : Fin 3, ∑ j : Fin 3, Q i j • U i j) := by
  simp only [smul_add,Finset.sum_add_distrib,Finset.smul_sum]
  exact congrArg (fun x : W => x+(∑ i : Fin 3, ∑ j : Fin 3, Q i j • U i j))
    (Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => smul_comm (Q i j) r⁻¹ (D i j))))

theorem sum_sub_kronecker_smul_of_diagonal_zero
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (Q : Fin 3 → Fin 3 → ℝ) (D : Fin 3 → Fin 3 → W)
    (hTrace : (∑ i : Fin 3, D i i)=0) :
    (∑ i : Fin 3, ∑ j : Fin 3, Q i j • D i j) =
      ∑ i : Fin 3, ∑ j : Fin 3, (Q i j-(if i=j then (1:ℝ) else 0)) • D i j := by
  have hDiag : (∑ i : Fin 3, ∑ j : Fin 3, (if i=j then (1:ℝ) else 0) • D i j)=0 := by
    simpa only [ite_smul,one_smul,zero_smul,Finset.sum_ite_eq,Finset.mem_univ,if_true] using hTrace
  simp only [sub_smul,Finset.sum_sub_distrib,hDiag,sub_zero]

theorem regroup_leading_regular_terms
    {W : Type*} [AddCommGroup W] (a b c d e : W) :
    (a+b+c)+(d-e)=a+(b+c+d-e) := by abel

end OAI.AnisotropicCalderon.ConstantFirstSectionCovariantAlgebra
