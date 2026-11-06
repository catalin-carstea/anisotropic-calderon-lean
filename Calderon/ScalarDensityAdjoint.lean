import Calderon.PrincipalDirectional
import Calderon.BaseDensityAdjoint
import Mathlib.LinearAlgebra.Matrix.Hermitian

noncomputable section
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.ScalarBaseAdjoint
open PrincipalCommutator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma directionalFDeriv_second_smul (i j : R3) (c : R3 → ℝ) (w : R3 → E)
    (hc : ContDiff ℝ ∞ c) (hw : ContDiff ℝ ∞ w) (x : R3) :
    directionalFDeriv j (directionalFDeriv i (fun y => c y • w y)) x =
      directionalFDeriv j (directionalFDeriv i c) x • w x +
      directionalFDeriv i c x • directionalFDeriv j w x +
      directionalFDeriv j c x • directionalFDeriv i w x +
      c x • directionalFDeriv j (directionalFDeriv i w) x := by
  have he : directionalFDeriv i (fun y => c y • w y) =
      fun y => directionalFDeriv i c y • w y + c y • directionalFDeriv i w y :=
    funext (fun y => directionalFDeriv_smul i c w hc hw y)
  rw [he, directionalFDeriv_add j (fun y => directionalFDeriv i c y • w y)
    (fun y => c y • directionalFDeriv i w y)
    ((contDiff_directionalFDeriv i c hc).smul hw)
    (hc.smul (contDiff_directionalFDeriv i w hw))]
  rw [directionalFDeriv_smul j _ _ (contDiff_directionalFDeriv i c hc) hw,
    directionalFDeriv_smul j _ _ hc (contDiff_directionalFDeriv i w hw)]
  abel

def scalarSecondBase (v : Fin 3 → R3) (a : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (u : R3 → E) (x : R3) : E :=
  ∑ i, ∑ j, a x i j • directionalFDeriv (v i) (directionalFDeriv (v j) u) x

def scalarSecondBaseAdjoint (v : Fin 3 → R3) (mu : R3 → ℝ)
    (a : R3 → Matrix (Fin 3) (Fin 3) ℝ) (w : R3 → E) (x : R3) : E :=
  (mu x)⁻¹ • ∑ i, ∑ j, directionalFDeriv (v j)
    (directionalFDeriv (v i) (fun y => (mu y * a y i j) • w y)) x

lemma compact_scalar_second_pair_integrable (i j : R3) (mu a : R3 → ℝ)
    (u w : R3 → E) (hm : ContDiff ℝ ∞ mu) (ha : ContDiff ℝ ∞ a)
    (hu : ContDiff ℝ ∞ u) (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport u) :
    Integrable (fun x => mu x * a x *
      ⟪directionalFDeriv i (directionalFDeriv j u) x, w x⟫_ℝ) := by
  have h := BaseDensityAdjoint.compact_inner_integrable
    (fun y => (mu y * a y) • w y) (directionalFDeriv i (directionalFDeriv j u))
    ((hm.mul ha).smul hw).continuous
    (contDiff_directionalFDeriv i _ (contDiff_directionalFDeriv j u hu)).continuous
    ((hc.fderiv_apply (𝕜 := ℝ) j).fderiv_apply (𝕜 := ℝ) i)
  simpa only [inner_smul_left, starRingEnd_apply, star_trivial, real_inner_comm] using h

lemma compact_scalar_second_adjoint_pair_integrable (i j : R3) (mu a : R3 → ℝ)
    (u w : R3 → E) (hm : ContDiff ℝ ∞ mu) (ha : ContDiff ℝ ∞ a)
    (hu : ContDiff ℝ ∞ u) (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport u) :
    Integrable (fun x => ⟪directionalFDeriv j
      (directionalFDeriv i (fun y => (mu y * a y) • w y)) x, u x⟫_ℝ) := by
  exact BaseDensityAdjoint.compact_inner_integrable _ u
    (contDiff_directionalFDeriv j _
      (contDiff_directionalFDeriv i _ ((hm.mul ha).smul hw))).continuous hu.continuous hc

theorem compact_scalarSecondBase_adjoint (v : Fin 3 → R3) (mu : R3 → ℝ)
    (a : R3 → Matrix (Fin 3) (Fin 3) ℝ) (u w : R3 → E)
    (hm : ContDiff ℝ ∞ mu) (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hu : ContDiff ℝ ∞ u) (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport u)
    (hp : ∀ x, 0 < mu x) :
    (∫ x : R3, mu x * ⟪scalarSecondBase v a u x, w x⟫_ℝ) =
      ∫ x : R3, mu x * ⟪u x, scalarSecondBaseAdjoint v mu a w x⟫_ℝ := by
  have hl : (∫ x : R3, mu x * ⟪scalarSecondBase v a u x, w x⟫_ℝ) =
      ∑ i, ∑ j, ∫ x : R3, mu x * a x i j *
        ⟪directionalFDeriv (v i) (directionalFDeriv (v j) u) x, w x⟫_ℝ := by
    simp only [scalarSecondBase, sum_inner, inner_smul_left, starRingEnd_apply,
      star_trivial, Finset.mul_sum, ← mul_assoc]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => compact_scalar_second_pair_integrable (v i) (v j) mu
        (fun y => a y i j) u w hm (ha i j) hu hw hc))]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum _ (fun j _ => compact_scalar_second_pair_integrable
      (v i) (v j) mu (fun y => a y i j) u w hm (ha i j) hu hw hc)
  have hr : (∫ x : R3, mu x * ⟪u x, scalarSecondBaseAdjoint v mu a w x⟫_ℝ) =
      ∑ i, ∑ j, ∫ x : R3, ⟪directionalFDeriv (v j)
        (directionalFDeriv (v i) (fun y => (mu y * a y i j) • w y)) x, u x⟫_ℝ := by
    have he : (fun x => mu x * ⟪u x, scalarSecondBaseAdjoint v mu a w x⟫_ℝ) =
        fun x => ∑ i, ∑ j, ⟪directionalFDeriv (v j)
          (directionalFDeriv (v i) (fun y => (mu y * a y i j) • w y)) x, u x⟫_ℝ := by
      funext x
      simp only [scalarSecondBaseAdjoint, inner_smul_right, inner_sum,
        Finset.mul_sum, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt (hp x)), one_mul]
      simp only [real_inner_comm]
    rw [he, integral_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => compact_scalar_second_adjoint_pair_integrable (v i) (v j) mu
        (fun y => a y i j) u w hm (ha i j) hu hw hc))]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum _ (fun j _ => compact_scalar_second_adjoint_pair_integrable
      (v i) (v j) mu (fun y => a y i j) u w hm (ha i j) hu hw hc)
  rw [hl, hr]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact BaseDensityAdjoint.compact_weighted_second_adjoint (v i) (v j) mu
    (fun y => a y i j) u w hm (ha i j) hu hw hc

lemma scalar_second_adjoint_term_difference (i j : R3) (mu a : R3 → ℝ)
    (w : R3 → E) (hm : ContDiff ℝ ∞ mu) (ha : ContDiff ℝ ∞ a)
    (hw : ContDiff ℝ ∞ w) (x : R3) (hp : mu x ≠ 0) :
    (mu x)⁻¹ • directionalFDeriv j
      (directionalFDeriv i (fun y => (mu y * a y) • w y)) x -
      a x • directionalFDeriv i (directionalFDeriv j w) x =
      (mu x)⁻¹ • (directionalFDeriv j (directionalFDeriv i (fun y => mu y * a y)) x • w x +
        directionalFDeriv i (fun y => mu y * a y) x • directionalFDeriv j w x +
        directionalFDeriv j (fun y => mu y * a y) x • directionalFDeriv i w x) := by
  rw [directionalFDeriv_second_smul i j _ w (hm.mul ha) hw,
    directionalFDeriv_commute j i w hw]
  simp only [smul_add, smul_smul]
  have he : (mu x)⁻¹ * (mu x * a x) = a x := by
    rw [← mul_assoc, inv_mul_cancel₀ hp, one_mul]
  rw [he]
  abel

lemma weighted_coefficient_directional_symmetry (v : R3) (mu : R3 → ℝ)
    (a : R3 → Matrix (Fin 3) (Fin 3) ℝ) (x : R3)
    (hs : ∀ᶠ y in 𝓝 x, (a y).IsHermitian) (i j : Fin 3) :
    directionalFDeriv v (fun y => mu y * a y i j) x =
      directionalFDeriv v (fun y => mu y * a y j i) x := by
  have he : (fun y => mu y * a y i j) =ᶠ[𝓝 x] (fun y => mu y * a y j i) := by
    filter_upwards [hs] with y hy
    have he : a y j i = a y i j := by simpa only [star_trivial] using hy.apply i j
    rw [he]
  exact congrArg (fun T : R3 →L[ℝ] ℝ => T v) he.fderiv_eq

lemma scalar_adjoint_cross_sum (v : Fin 3 → R3) (mu : R3 → ℝ)
    (a : R3 → Matrix (Fin 3) (Fin 3) ℝ) (w : R3 → E) (x : R3)
    (hs : ∀ᶠ y in 𝓝 x, (a y).IsHermitian) :
    (∑ i, ∑ j, directionalFDeriv (v i) (fun y => mu y * a y i j) x •
      directionalFDeriv (v j) w x) =
    ∑ i, ∑ j, directionalFDeriv (v j) (fun y => mu y * a y i j) x •
      directionalFDeriv (v i) w x := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [weighted_coefficient_directional_symmetry (v j) mu a x hs j i]

theorem scalarSecondBaseAdjoint_sub (v : Fin 3 → R3) (mu : R3 → ℝ)
    (a : R3 → Matrix (Fin 3) (Fin 3) ℝ) (w : R3 → E)
    (hm : ContDiff ℝ ∞ mu) (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hw : ContDiff ℝ ∞ w) (x : R3) (hp : mu x ≠ 0)
    (hs : ∀ᶠ y in 𝓝 x, (a y).IsHermitian) :
    scalarSecondBaseAdjoint v mu a w x - scalarSecondBase v a w x =
      (mu x)⁻¹ • (∑ i, ∑ j, directionalFDeriv (v j)
        (directionalFDeriv (v i) (fun y => mu y * a y i j)) x • w x) +
      (2 * (mu x)⁻¹) • (∑ i, ∑ j,
        directionalFDeriv (v j) (fun y => mu y * a y i j) x •
        directionalFDeriv (v i) w x) := by
  calc
    _ = ∑ i, ∑ j, ((mu x)⁻¹ • directionalFDeriv (v j)
        (directionalFDeriv (v i) (fun y => (mu y * a y i j) • w y)) x -
        a x i j • directionalFDeriv (v i) (directionalFDeriv (v j) w) x) := by
      simp only [scalarSecondBaseAdjoint, scalarSecondBase, Finset.smul_sum,
        Finset.sum_sub_distrib]
    _ = ∑ i, ∑ j, ((mu x)⁻¹ •
        (directionalFDeriv (v j) (directionalFDeriv (v i) (fun y => mu y * a y i j)) x • w x +
        directionalFDeriv (v i) (fun y => mu y * a y i j) x • directionalFDeriv (v j) w x +
        directionalFDeriv (v j) (fun y => mu y * a y i j) x • directionalFDeriv (v i) w x)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact scalar_second_adjoint_term_difference (v i) (v j) mu
        (fun y => a y i j) w hm (ha i j) hw x hp
    _ = _ := by
      simp only [← Finset.smul_sum, Finset.sum_add_distrib]
      rw [scalar_adjoint_cross_sum v mu a w x hs]
      module

end OAI.AnisotropicCalderon.ScalarBaseAdjoint
