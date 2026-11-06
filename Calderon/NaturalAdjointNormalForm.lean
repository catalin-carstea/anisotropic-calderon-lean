import Calderon.NaturalFullAdjointReduction

set_option autoImplicit false
noncomputable section
open Filter
open scoped ContDiff
namespace OAI.AnisotropicCalderon.NaturalAngularAdjoint
open PrincipalCommutator ScalarBaseAdjoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma directionalFDeriv_fintype_sum {ι : Type*} [Fintype ι] (X : R3) (u : ι → R3 → E)
    (hu : ∀ i, ContDiff ℝ ∞ (u i)) (x : R3) :
    directionalFDeriv X (fun y => ∑ i, u i y) x =
      ∑ i, directionalFDeriv X (u i) x := by
  classical
  unfold directionalFDeriv
  rw [fderiv_fun_sum (fun i _ => (hu i).differentiable (by simp) x)]
  simp only [sum_apply]

lemma directionalFDeriv_second_fintype_sum {ι : Type*} [Fintype ι] (X Y : R3)
    (u : ι → R3 → E) (hu : ∀ i, ContDiff ℝ ∞ (u i)) (x : R3) :
    directionalFDeriv X (directionalFDeriv Y (fun y => ∑ i, u i y)) x =
      ∑ i, directionalFDeriv X (directionalFDeriv Y (u i)) x := by
  have he : directionalFDeriv Y (fun y => ∑ i, u i y) =
      fun y => ∑ i, directionalFDeriv Y (u i) y :=
    funext (directionalFDeriv_fintype_sum Y u hu)
  rw [he]
  exact directionalFDeriv_fintype_sum X _ (fun i => contDiff_directionalFDeriv Y (u i) (hu i)) x

def firstPrincipalRemainder (v : Fin 3 → R3) (a : MatrixField)
    (G : Fin 3 → R3 → E →L[ℝ] E) (w : R3 → E) (x : R3) : E :=
  ∑ k, ∑ i, ∑ j, (
    directionalFDeriv (v k) (fun y => a y i j) x •
      G k x (directionalFDeriv (v i) (directionalFDeriv (v j) w) x) -
    a x i j • directionalFDeriv (v i) (directionalFDeriv (v j) (G k)) x
      (directionalFDeriv (v k) w x) -
    a x i j • directionalFDeriv (v j) (G k) x
      (directionalFDeriv (v i) (directionalFDeriv (v k) w) x) -
    a x i j • directionalFDeriv (v i) (G k) x
      (directionalFDeriv (v j) (directionalFDeriv (v k) w) x))

def zeroPrincipalRemainder (v : Fin 3 → R3) (a : MatrixField)
    (H : R3 → E →L[ℝ] E) (w : R3 → E) (x : R3) : E :=
  ∑ i, ∑ j, (
    -a x i j • directionalFDeriv (v i) (directionalFDeriv (v j) H) x (w x) -
    a x i j • directionalFDeriv (v j) H x (directionalFDeriv (v i) w x) -
    a x i j • directionalFDeriv (v i) H x (directionalFDeriv (v j) w x))

def firstFirstRemainder (v : Fin 3 → R3) (G B : Fin 3 → R3 → E →L[ℝ] E)
    (w : R3 → E) (x : R3) : E :=
  ∑ k, ∑ i, (
    G k x (directionalFDeriv (v k) (B i) x (directionalFDeriv (v i) w x)) -
      B i x (directionalFDeriv (v i) (G k) x (directionalFDeriv (v k) w x)) +
      ((G k x).comp (B i x) - (B i x).comp (G k x))
        (directionalFDeriv (v k) (directionalFDeriv (v i) w) x))

def zeroFirstRemainder (v : Fin 3 → R3) (H : R3 → E →L[ℝ] E)
    (B : Fin 3 → R3 → E →L[ℝ] E) (w : R3 → E) (x : R3) : E :=
  ∑ i, (((H x).comp (B i x) - (B i x).comp (H x)) (directionalFDeriv (v i) w x) -
    B i x (directionalFDeriv (v i) H x (w x)))

def firstZeroRemainder (v : Fin 3 → R3) (G : Fin 3 → R3 → E →L[ℝ] E)
    (C : R3 → E →L[ℝ] E) (w : R3 → E) (x : R3) : E :=
  ∑ k, (G k x (directionalFDeriv (v k) C x (w x)) +
    ((G k x).comp (C x) - (C x).comp (G k x)) (directionalFDeriv (v k) w x))

/-- Transparent normal form: every section derivative in these six summands
 has ordinary base order zero, one or two. Angular commutators are retained. -/
def secondBaseCommutatorRemainder (v : Fin 3 → R3) (a : MatrixField)
    (G : Fin 3 → R3 → E →L[ℝ] E) (H : R3 → E →L[ℝ] E)
    (B : Fin 3 → R3 → E →L[ℝ] E) (C : R3 → E →L[ℝ] E)
    (w : R3 → E) (x : R3) : E :=
  firstPrincipalRemainder v a G w x + zeroPrincipalRemainder v a H w x +
    firstFirstRemainder v G B w x + zeroFirstRemainder v H B w x +
    firstZeroRemainder v G C w x + ((H x).comp (C x) - (C x).comp (H x)) (w x)

lemma angularFirstBase_scalarSecondBase_commutator (v : Fin 3 → R3) (a : MatrixField)
    (G : Fin 3 → R3 → E →L[ℝ] E) (w : R3 → E)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hG : ∀ k, ContDiff ℝ ∞ (G k)) (hw : ContDiff ℝ ∞ w) (x : R3) :
    angularFirstBase v G (scalarSecondBase v a w) x -
      scalarSecondBase v a (angularFirstBase v G w) x = firstPrincipalRemainder v a G w x := by
  have hs (X : R3) : directionalFDeriv X (scalarSecondBase v a w) =
      fun y => ∑ i, ∑ j, directionalFDeriv X
        (fun z => a z i j • directionalFDeriv (v i) (directionalFDeriv (v j) w) z) y := by
    funext y
    let F : Fin 3 → Fin 3 → R3 → E := fun i j z =>
      a z i j • directionalFDeriv (v i) (directionalFDeriv (v j) w) z
    have hF (i j : Fin 3) : ContDiff ℝ ∞ (F i j) :=
      (ha i j).smul (contDiff_directionalFDeriv (v i) _ (contDiff_directionalFDeriv (v j) w hw))
    have hsum (i : Fin 3) : ContDiff ℝ ∞ (fun z => ∑ j : Fin 3, F i j z) :=
      ContDiff.sum (f := F i) (s := Finset.univ) (fun j _ => hF i j)
    change directionalFDeriv X (fun z => ∑ i : Fin 3, ∑ j : Fin 3, F i j z) y = _
    rw [directionalFDeriv_fintype_sum X (fun i z => ∑ j : Fin 3, F i j z) hsum y]
    apply Finset.sum_congr rfl
    intro i _
    exact directionalFDeriv_fintype_sum X (F i) (hF i) y
  have ht (X Y : R3) : directionalFDeriv X (directionalFDeriv Y (angularFirstBase v G w)) =
      fun y => ∑ k, directionalFDeriv X (directionalFDeriv Y
        (fun z => G k z (directionalFDeriv (v k) w z))) y := by
    funext y
    exact directionalFDeriv_second_fintype_sum X Y _
      (fun k => (hG k).clm_apply (contDiff_directionalFDeriv (v k) w hw)) y
  change (∑ k, G k x (directionalFDeriv (v k) (scalarSecondBase v a w) x)) -
    (∑ i, ∑ j, a x i j • directionalFDeriv (v i)
      (directionalFDeriv (v j) (angularFirstBase v G w)) x) = _
  simp_rw [hs, ht, map_sum, Finset.smul_sum]
  have he : (∑ i, ∑ j, ∑ k, a x i j • directionalFDeriv (v i)
        (directionalFDeriv (v j) (fun z => G k z (directionalFDeriv (v k) w z))) x) =
      ∑ k, ∑ i, ∑ j, a x i j • directionalFDeriv (v i)
        (directionalFDeriv (v j) (fun z => G k z (directionalFDeriv (v k) w z))) x := by
    calc
      _ = ∑ i, ∑ k, ∑ j, a x i j • directionalFDeriv (v i)
          (directionalFDeriv (v j) (fun z => G k z (directionalFDeriv (v k) w z))) x := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  unfold firstPrincipalRemainder
  rw [he, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  exact scalar_principal_directional_commutator (v i) (v j) (v k)
    (fun y => a y i j) (G k) w (ha i j) (hG k) hw x

lemma zero_scalarSecondBase_commutator (v : Fin 3 → R3) (a : MatrixField)
    (H : R3 → E →L[ℝ] E) (w : R3 → E)
    (hH : ContDiff ℝ ∞ H) (hw : ContDiff ℝ ∞ w) (x : R3) :
    H x (scalarSecondBase v a w x) -
      scalarSecondBase v a (fun y => H y (w y)) x = zeroPrincipalRemainder v a H w x := by
  simp only [scalarSecondBase, zeroPrincipalRemainder, map_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact zero_scalar_second_commutator (v i) (v j) (fun y => a y i j) H w hH hw x

lemma angularFirstBase_commutator (v : Fin 3 → R3) (G B : Fin 3 → R3 → E →L[ℝ] E)
    (w : R3 → E) (hG : ∀ k, ContDiff ℝ ∞ (G k))
    (hB : ∀ i, ContDiff ℝ ∞ (B i)) (hw : ContDiff ℝ ∞ w) (x : R3) :
    angularFirstBase v G (angularFirstBase v B w) x -
      angularFirstBase v B (angularFirstBase v G w) x = firstFirstRemainder v G B w x := by
  have hs (A : Fin 3 → R3 → E →L[ℝ] E) (hA : ∀ i, ContDiff ℝ ∞ (A i)) (X : R3) :
      directionalFDeriv X (angularFirstBase v A w) =
      fun y => ∑ i, directionalFDeriv X (fun z => A i z (directionalFDeriv (v i) w z)) y := by
    funext y
    exact directionalFDeriv_fintype_sum X _
      (fun i => (hA i).clm_apply (contDiff_directionalFDeriv (v i) w hw)) y
  change (∑ k, G k x (directionalFDeriv (v k) (angularFirstBase v B w) x)) -
    (∑ i, B i x (directionalFDeriv (v i) (angularFirstBase v G w) x)) = _
  simp_rw [hs B hB, hs G hG, map_sum]
  conv_lhs => rhs; rw [Finset.sum_comm]
  unfold firstFirstRemainder
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact first_first_commutator (v i) (v k) (G k) (B i) w (hG k) (hB i) hw x

lemma zero_angularFirstBase_commutator (v : Fin 3 → R3) (H : R3 → E →L[ℝ] E)
    (B : Fin 3 → R3 → E →L[ℝ] E) (w : R3 → E)
    (hH : ContDiff ℝ ∞ H) (hw : ContDiff ℝ ∞ w) (x : R3) :
    H x (angularFirstBase v B w x) - angularFirstBase v B (fun y => H y (w y)) x =
      zeroFirstRemainder v H B w x := by
  simp only [angularFirstBase, zeroFirstRemainder, map_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact zero_first_commutator (v i) H (B i) w hH hw x

lemma angularFirstBase_zero_commutator (v : Fin 3 → R3) (G : Fin 3 → R3 → E →L[ℝ] E)
    (C : R3 → E →L[ℝ] E) (w : R3 → E)
    (hC : ContDiff ℝ ∞ C) (hw : ContDiff ℝ ∞ w) (x : R3) :
    angularFirstBase v G (fun y => C y (w y)) x - C x (angularFirstBase v G w x) =
      firstZeroRemainder v G C w x := by
  simp only [angularFirstBase, firstZeroRemainder, map_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  exact first_zero_commutator (v k) (G k) C w hC hw x

def firstZeroOperator (v : Fin 3 → R3) (G : Fin 3 → R3 → E →L[ℝ] E)
    (H : R3 → E →L[ℝ] E) (w : R3 → E) (x : R3) : E :=
  angularFirstBase v G w x + H x (w x)

lemma firstZeroOperator_add (v : Fin 3 → R3) (G : Fin 3 → R3 → E →L[ℝ] E)
    (H : R3 → E →L[ℝ] E) (u w : R3 → E)
    (hu : ContDiff ℝ ∞ u) (hw : ContDiff ℝ ∞ w) (x : R3) :
    firstZeroOperator v G H (fun y => u y + w y) x =
      firstZeroOperator v G H u x + firstZeroOperator v G H w x := by
  simp only [firstZeroOperator, angularFirstBase]
  simp_rw [directionalFDeriv_add _ u w hu hw x, map_add, Finset.sum_add_distrib]
  abel

/-- Full finite-summed commutator normal form, with no third-base section derivative. -/
theorem firstZeroOperator_naturalOperator_commutator (v : Fin 3 → R3) (a : MatrixField)
    (G : Fin 3 → R3 → E →L[ℝ] E) (H : R3 → E →L[ℝ] E)
    (B : Fin 3 → R3 → E →L[ℝ] E) (C : R3 → E →L[ℝ] E) (w : R3 → E)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hG : ∀ k, ContDiff ℝ ∞ (G k)) (hH : ContDiff ℝ ∞ H)
    (hB : ∀ i, ContDiff ℝ ∞ (B i)) (hC : ContDiff ℝ ∞ C)
    (hw : ContDiff ℝ ∞ w) (x : R3) :
    firstZeroOperator v G H (naturalOperator v a B C w) x -
      naturalOperator v a B C (firstZeroOperator v G H w) x =
      secondBaseCommutatorRemainder v a G H B C w x := by
  have hs := contDiff_scalarSecondBase v a w ha hw
  have hfb := contDiff_angularFirstBase v B w hB hw
  have hfg := contDiff_angularFirstBase v G w hG hw
  have hcw := hC.clm_apply hw
  have hhw := hH.clm_apply hw
  have hl : firstZeroOperator v G H (naturalOperator v a B C w) x =
      firstZeroOperator v G H (scalarSecondBase v a w) x +
      firstZeroOperator v G H (angularFirstBase v B w) x +
      firstZeroOperator v G H (fun y => C y (w y)) x := by
    unfold naturalOperator
    rw [firstZeroOperator_add v G H _ _ (hs.add hfb) hcw x,
      firstZeroOperator_add v G H _ _ hs hfb x]
  have hr : naturalOperator v a B C (firstZeroOperator v G H w) x =
      naturalOperator v a B C (angularFirstBase v G w) x +
      naturalOperator v a B C (fun y => H y (w y)) x := by
    exact naturalOperator_add v a B C _ _ hfg hhw x
  calc
    _ = (angularFirstBase v G (scalarSecondBase v a w) x -
          scalarSecondBase v a (angularFirstBase v G w) x) +
        (H x (scalarSecondBase v a w x) - scalarSecondBase v a (fun y => H y (w y)) x) +
        (angularFirstBase v G (angularFirstBase v B w) x -
          angularFirstBase v B (angularFirstBase v G w) x) +
        (H x (angularFirstBase v B w x) - angularFirstBase v B (fun y => H y (w y)) x) +
        (angularFirstBase v G (fun y => C y (w y)) x - C x (angularFirstBase v G w x)) +
        (H x (C x (w x)) - C x (H x (w x))) := by
      rw [hl, hr]
      unfold firstZeroOperator naturalOperator
      abel
    _ = _ := by
      rw [angularFirstBase_scalarSecondBase_commutator v a G w ha hG hw x,
        zero_scalarSecondBase_commutator v a H w hH hw x,
        angularFirstBase_commutator v G B w hG hB hw x,
        zero_angularFirstBase_commutator v H B w hH hw x,
        angularFirstBase_zero_commutator v G C w hC hw x]
      rfl

lemma naturalAdjointDefect_eq_firstZeroOperator (v : Fin 3 → R3) (mu : R3 → ℝ)
    (a : MatrixField) (B : Fin 3 → R3 → E →L[ℝ] E) (C : R3 → E →L[ℝ] E)
    (w : R3 → E) :
    naturalAdjointDefect v mu a B C w =
      firstZeroOperator v (fun i y => defectFirstCoefficient v mu a B y i)
        (defectZeroCoefficient v mu a B C) w := by
  funext x
  exact add_comm _ _

/-- The full computed density/angular adjoint commutator has the transparent
 second-base normal form. Its angular order and quantitative form estimates are open. -/
theorem naturalFullAdjoint_commutator_normal_form (v : Fin 3 → R3)
    (mu : R3 → ℝ) (a : MatrixField) (B : Fin 3 → R3 → E →L[ℝ] E)
    (C : R3 → E →L[ℝ] E) (w : R3 → E)
    (hm : ContDiff ℝ ∞ mu) (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hB : ∀ i, ContDiff ℝ ∞ (B i)) (hC : ContDiff ℝ ∞ C)
    (hw : ContDiff ℝ ∞ w) (hp : ∀ x, mu x ≠ 0)
    (hs : ∀ x, (a x).IsHermitian) (x : R3) :
    naturalFormalAdjoint v mu a B C (naturalOperator v a B C w) x -
      naturalOperator v a B C (naturalFormalAdjoint v mu a B C w) x =
    secondBaseCommutatorRemainder v a (fun i y => defectFirstCoefficient v mu a B y i)
      (defectZeroCoefficient v mu a B C) B C w x := by
  rw [naturalFullAdjoint_commutator_eq_defect_commutator v mu a B C w hm ha hB hC hw hp hs x,
    naturalAdjointDefect_eq_firstZeroOperator, naturalAdjointDefect_eq_firstZeroOperator]
  exact firstZeroOperator_naturalOperator_commutator v a _ _ B C w ha
    (fun i => contDiff_defectFirstCoefficient v mu a B hm ha hB hp i)
    (contDiff_defectZeroCoefficient v mu a B C hm ha hB hC hp) hB hC hw x

end OAI.AnisotropicCalderon.NaturalAngularAdjoint
