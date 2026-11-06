import Calderon.ActualDensityScalarCutoff
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

private lemma norm_scaled_sum_le {ι V : Type*} [Fintype ι]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (r : ℝ) (F : ι → V) :
    ‖r • ∑ i, F i‖ ≤ ∑ i, ‖r • F i‖ := by
  classical
  rw [Finset.smul_sum]
  exact norm_sum_le _ _

private lemma norm_scalar_shuffle {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (r a : ℝ) (v : V) :
    ‖r • (a • v)‖ = |a| * ‖r • v‖ := by
  rw [smul_comm r a v,norm_smul,Real.norm_eq_abs]

theorem norm_scalarCutoffCommutator_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (r : ℝ) (a h : Fin 3 → Fin 3 → ℝ) (d b : Fin 3 → ℝ)
    (U : Fin 3 → V) (w : V) (M B : ℝ)
    (hM : 1 ≤ M) (hB : 0 ≤ B) (hr : |r| ≤ M) (hw : ‖w‖ ≤ M)
    (ha : ∀ i j, |a i j| ≤ M) (hd : ∀ i, |d i| ≤ M)
    (hh : ∀ i j, |h i j| ≤ M) (hb : ∀ i, |b i| ≤ M)
    (hU : ∀ i, ‖r • U i‖ ≤ B) :
    ‖r • ((∑ i : Fin 3, ∑ j : Fin 3,
      a i j • (d i • U j+d j • U i+h i j • w)) +
      ∑ i : Fin 3, b i • (d i • w))‖ ≤
      9*(M*(M*B+M*B+M*M*M))+3*(M*M*M*M) := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hRw : ‖r • w‖ ≤ M*M := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hr hw (norm_nonneg w) hM0
  have hDU (i j : Fin 3) : ‖r • (d i • U j)‖ ≤ M*B := by
    rw [norm_scalar_shuffle]
    exact mul_le_mul (hd i) (hU j) (norm_nonneg _) hM0
  have hHW (i j : Fin 3) : ‖r • (h i j • w)‖ ≤ M*M*M := by
    rw [norm_scalar_shuffle]
    simpa only [mul_assoc] using mul_le_mul (hh i j) hRw (norm_nonneg _) hM0
  have hInner (i j : Fin 3) :
      ‖r • (d i • U j+d j • U i+h i j • w)‖ ≤ M*B+M*B+M*M*M := by
    rw [smul_add,smul_add]
    have h1 := norm_add_le (r • (d i • U j)) (r • (d j • U i))
    have h2 := norm_add_le (r • (d i • U j)+r • (d j • U i)) (r • (h i j • w))
    linarith only [h1,h2,hDU i j,hDU j i,hHW i j]
  have hPrincipal (i j : Fin 3) :
      ‖r • (a i j • (d i • U j+d j • U i+h i j • w))‖ ≤
        M*(M*B+M*B+M*M*M) := by
    rw [norm_scalar_shuffle]
    exact mul_le_mul (ha i j) (hInner i j) (norm_nonneg _) hM0
  have hP : ‖r • ∑ i : Fin 3, ∑ j : Fin 3,
      a i j • (d i • U j+d j • U i+h i j • w)‖ ≤
      9*(M*(M*B+M*B+M*M*M)) := by
    calc
      _ ≤ ∑ i : Fin 3, ‖r • ∑ j : Fin 3,
          a i j • (d i • U j+d j • U i+h i j • w)‖ := norm_scaled_sum_le _ _
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          ‖r • (a i j • (d i • U j+d j • U i+h i j • w))‖ :=
        Finset.sum_le_sum (fun i _ => norm_scaled_sum_le _ _)
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, M*(M*B+M*B+M*M*M) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hPrincipal i j))
      _ = _ := by simp <;> ring
  have hDW (i : Fin 3) : ‖r • (d i • w)‖ ≤ M*M*M := by
    rw [norm_scalar_shuffle]
    simpa only [mul_assoc] using mul_le_mul (hd i) hRw (norm_nonneg _) hM0
  have hDrift (i : Fin 3) : ‖r • (b i • (d i • w))‖ ≤ M*M*M*M := by
    rw [norm_scalar_shuffle]
    simpa only [mul_assoc] using mul_le_mul (hb i) (hDW i) (norm_nonneg _) hM0
  have hD : ‖r • ∑ i : Fin 3, b i • (d i • w)‖ ≤ 3*(M*M*M*M) := by
    calc
      _ ≤ ∑ i : Fin 3, ‖r • (b i • (d i • w))‖ := norm_scaled_sum_le _ _
      _ ≤ ∑ i : Fin 3, M*M*M*M := Finset.sum_le_sum (fun i _ => hDrift i)
      _ = _ := by simp <;> ring
  rw [smul_add]
  exact (norm_add_le _ _).trans (add_le_add hP hD)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
