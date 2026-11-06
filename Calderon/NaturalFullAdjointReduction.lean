import Calderon.NaturalAdjointCommutator

set_option autoImplicit false
noncomputable section
open Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.NaturalAngularAdjoint
open PrincipalCommutator ScalarBaseAdjoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The computed full-density/angular-adjoint defect as an actual differential operator. -/
def naturalAdjointDefect (v : Fin 3 → R3) (mu : R3 → ℝ) (a : MatrixField)
    (B : Fin 3 → R3 → E →L[ℝ] E) (C : R3 → E →L[ℝ] E)
    (w : R3 → E) (x : R3) : E :=
  defectZeroCoefficient v mu a B C x (w x) +
    ∑ i, defectFirstCoefficient v mu a B x i (directionalFDeriv (v i) w x)

lemma contDiff_naturalOperator (v : Fin 3 → R3) (a : MatrixField)
    (B : Fin 3 → R3 → E →L[ℝ] E) (C : R3 → E →L[ℝ] E) (w : R3 → E)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hB : ∀ i, ContDiff ℝ ∞ (B i)) (hC : ContDiff ℝ ∞ C) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (naturalOperator v a B C w) := by
  exact ((contDiff_scalarSecondBase v a w ha hw).add
    (contDiff_angularFirstBase v B w hB hw)).add (hC.clm_apply hw)

lemma contDiff_naturalAdjointDefect (v : Fin 3 → R3) (mu : R3 → ℝ) (a : MatrixField)
    (B : Fin 3 → R3 → E →L[ℝ] E) (C : R3 → E →L[ℝ] E) (w : R3 → E)
    (hm : ContDiff ℝ ∞ mu) (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hB : ∀ i, ContDiff ℝ ∞ (B i)) (hC : ContDiff ℝ ∞ C)
    (hw : ContDiff ℝ ∞ w) (hp : ∀ x, mu x ≠ 0) :
    ContDiff ℝ ∞ (naturalAdjointDefect v mu a B C w) := by
  exact ((contDiff_defectZeroCoefficient v mu a B C hm ha hB hC hp).clm_apply hw).add
    (contDiff_angularFirstBase v (fun i y => defectFirstCoefficient v mu a B y i) w
      (fun i => contDiff_defectFirstCoefficient v mu a B hm ha hB hp i) hw)

lemma directionalFDeriv_second_add (i j : R3) (u w : R3 → E)
    (hu : ContDiff ℝ ∞ u) (hw : ContDiff ℝ ∞ w) (x : R3) :
    directionalFDeriv i (directionalFDeriv j (fun y => u y + w y)) x =
      directionalFDeriv i (directionalFDeriv j u) x +
      directionalFDeriv i (directionalFDeriv j w) x := by
  have he : directionalFDeriv j (fun y => u y + w y) =
      fun y => directionalFDeriv j u y + directionalFDeriv j w y :=
    funext (directionalFDeriv_add j u w hu hw)
  rw [he, directionalFDeriv_add i _ _ (contDiff_directionalFDeriv j u hu)
    (contDiff_directionalFDeriv j w hw)]

lemma naturalOperator_add (v : Fin 3 → R3) (a : MatrixField)
    (B : Fin 3 → R3 → E →L[ℝ] E) (C : R3 → E →L[ℝ] E) (u w : R3 → E)
    (hu : ContDiff ℝ ∞ u) (hw : ContDiff ℝ ∞ w) (x : R3) :
    naturalOperator v a B C (fun y => u y + w y) x =
      naturalOperator v a B C u x + naturalOperator v a B C w x := by
  simp only [naturalOperator, scalarSecondBase, angularFirstBase]
  simp_rw [directionalFDeriv_second_add _ _ u w hu hw x,
    directionalFDeriv_add _ u w hu hw x, smul_add, map_add, Finset.sum_add_distrib]
  abel

lemma naturalFormalAdjoint_eq_operator_add_defect (v : Fin 3 → R3)
    (mu : R3 → ℝ) (a : MatrixField) (B : Fin 3 → R3 → E →L[ℝ] E)
    (C : R3 → E →L[ℝ] E) (w : R3 → E)
    (hm : ContDiff ℝ ∞ mu) (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hB : ∀ i, ContDiff ℝ ∞ (B i)) (hw : ContDiff ℝ ∞ w)
    (hp : ∀ x, mu x ≠ 0) (hs : ∀ x, (a x).IsHermitian) :
    naturalFormalAdjoint v mu a B C w =
      fun x => naturalOperator v a B C w x + naturalAdjointDefect v mu a B C w x := by
  funext x
  have h := naturalFormalAdjoint_sub v mu a B C w hm ha hB hw x (hp x)
    (Filter.Eventually.of_forall hs)
  change naturalFormalAdjoint v mu a B C w x = _
  change naturalFormalAdjoint v mu a B C w x - naturalOperator v a B C w x =
    naturalAdjointDefect v mu a B C w x at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

/-- Exact source reduction [U†,U]=[U†−U,U] on the declared smooth Hilbert domain.
 The right operator is the computed first/zero defect, not an assumed discrepancy. -/
theorem naturalFullAdjoint_commutator_eq_defect_commutator (v : Fin 3 → R3)
    (mu : R3 → ℝ) (a : MatrixField) (B : Fin 3 → R3 → E →L[ℝ] E)
    (C : R3 → E →L[ℝ] E) (w : R3 → E)
    (hm : ContDiff ℝ ∞ mu) (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hB : ∀ i, ContDiff ℝ ∞ (B i)) (hC : ContDiff ℝ ∞ C)
    (hw : ContDiff ℝ ∞ w) (hp : ∀ x, mu x ≠ 0)
    (hs : ∀ x, (a x).IsHermitian) (x : R3) :
    naturalFormalAdjoint v mu a B C (naturalOperator v a B C w) x -
      naturalOperator v a B C (naturalFormalAdjoint v mu a B C w) x =
    naturalAdjointDefect v mu a B C (naturalOperator v a B C w) x -
      naturalOperator v a B C (naturalAdjointDefect v mu a B C w) x := by
  have hU := contDiff_naturalOperator v a B C w ha hB hC hw
  have hD := contDiff_naturalAdjointDefect v mu a B C w hm ha hB hC hw hp
  rw [naturalFormalAdjoint_eq_operator_add_defect v mu a B C
    (naturalOperator v a B C w) hm ha hB hU hp hs,
    naturalFormalAdjoint_eq_operator_add_defect v mu a B C w hm ha hB hw hp hs,
    naturalOperator_add v a B C (naturalOperator v a B C w)
      (naturalAdjointDefect v mu a B C w) hU hD x]
  simp only [add_sub_add_left_eq_sub]

end OAI.AnisotropicCalderon.NaturalAngularAdjoint
