import Calderon.ActualMixedDensityScalarZeroForm
import Calderon.ActualReferenceDDHigherProfileJets
import Calderon.ActualMixedDensityScalarZeroFactorSmoothness

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualNormalizedPrincipalDensityCoefficientJets
open SphereHarmonic CoordinateBootstrapJets ReferenceDensityBounds PrincipalCommutator ActualHorizontalNormBridge
  ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherProfileJets
  ActualMixedDensityHigherCoefficientJets ActualMixedDensityScalarZeroForm
  NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth ActualScalarPrincipalAdjoint
  ConformalDepth RadiusProfile ReferenceWeightedApproximation

/-- This predicate refers to literal actual softplus radius words and beta.
Its native uniform witness is constructed separately, before any coefficient estimate. -/
def ActualRadiusCoordinateJetBound (g : MatrixField) (L lam δ R : ℝ) (p : ℕ)
    (x : R3) (Cr : ℝ) (N : ℕ) : Prop :=
  ∀ w : List (Fin 3), w.length ≤ N →
    |coordinateFieldWordPartial w (referenceRadius δ R p L) x| ≤
      Cr*referenceRadius δ R p L x*(actualReferenceBeta g L lam δ R p x)^w.length

def normalizedPrincipalCoordinateJetConstant (N : ℕ) : ℝ := (2 : ℝ)^(N+1)

def weightedNormalizedPrincipalCoordinateJetConstant (N : ℕ) : ℝ :=
  (2 : ℝ)^N*normalizedPrincipalCoordinateJetConstant N

def scalarAdjointFirstCoordinateJetConstant (N : ℕ) : ℝ :=
  6*(2 : ℝ)^N*weightedNormalizedPrincipalCoordinateJetConstant (N+1)

def scalarAdjointZeroCoordinateJetConstant (N : ℕ) : ℝ :=
  9*(2 : ℝ)^N*weightedNormalizedPrincipalCoordinateJetConstant (N+2)

theorem exists_actual_radius_coordinate_jet_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) (N : ℕ) :
    ∃ Cr : ℝ, 0 < Cr ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R →
      ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
        ActualRadiusCoordinateJetBound g L lam δ R p x Cr N := by
  obtain ⟨Cr,hCr,hBounds⟩ := exists_referenceRadius_uniform_coordinate_word_bounds g hg L hL K hK N
  refine ⟨Cr,hCr,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx w hw
  simpa only [actualReferenceBeta] using (hBounds lam hlam δ hδ hδ1 R hR p hp x hx w hw).1

/-- Actual a=rQ coordinate jets; genuine radius and Q=h+inverse witnesses
are used rather than assuming a principal coefficient remainder bound. -/
theorem abs_actualNormalizedPrincipal_coordinate_word_le
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (x : R3) (eps M Cr : ℝ) (N : ℕ) (hN : N ≤ 8)
    (hδ : 0 < δ) (hR : 0 < R) (heps : 0 ≤ eps) (hM : 1 ≤ M) (hCr : 0 ≤ Cr)
    (hsmall : eps*referenceRadius δ R p L x ≤ 1)
    (hbeta : 1 ≤ actualReferenceBeta g1 L lam δ R p x)
    (hgeom : MixedPrincipalDensityBackgroundJetBound g1 L lam x M N)
    (hRadius : ActualRadiusCoordinateJetBound g1 L lam δ R p x Cr N)
    (hH8 : coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
      eps*referenceRadius δ R p L x)
    (w : List (Fin 3)) (hw : w.length ≤ N) (i j : Fin 3) :
    |coordinateFieldWordPartial w
      (fun y => actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam) y i j) x| ≤
      normalizedPrincipalCoordinateJetConstant N*Cr*M*referenceRadius δ R p L x*
        (actualReferenceBeta g1 L lam δ R p x)^w.length := by
  let r : R3 → ℝ := referenceRadius δ R p L
  let Q : R3 → ℝ := fun y => referenceNormalizedPrincipalMatrix g1 g2 L lam y i j
  let beta : ℝ := actualReferenceBeta g1 L lam δ R p x
  let A : ℝ := Cr*r x*beta^w.length
  have hr : 0 < r x := referenceRadius_pos δ R p L x hδ hR
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hb0 : 0 ≤ beta := le_trans zero_le_one hbeta
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hRsm : ContDiff ℝ ∞ r := contDiff_referenceRadius_actual δ R p L hδ hR
  have hQsm : ContDiff ℝ ∞ Q :=
    contDiff_referenceNormalizedPrincipalMatrix_entry_slice g1 g2 hg1 hg2 L lam i j
  have haEq : (fun y => actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam) y i j) =
      fun y => r y*Q y := by
    funext y
    rw [actualPrincipalMatrix_normalized_eq]
    rfl
  have hrj (v : List (Fin 3)) (hv : v.length ≤ w.length) : |coordinateFieldWordPartial v r x| ≤ A := by
    have ht := hRadius v (le_trans hv hw)
    have hpow : beta^v.length ≤ beta^w.length := pow_le_pow_right₀ hbeta hv
    exact ht.trans (mul_le_mul_of_nonneg_left hpow (mul_nonneg hCr hr.le))
  have hQj (v : List (Fin 3)) (hv : v.length ≤ w.length) : |coordinateFieldWordPartial v Q x| ≤ 2*M :=
    abs_referenceNormalizedPrincipalMatrix_coordinate_word_le g1 g2 hg1 hg2 L lam x
      eps (r x) M N hN hM hsmall hgeom hH8 v (le_trans hv hw) i j
  have h := abs_coordinateFieldWordPartial_mul_le w r Q hRsm hQsm x A (2*M) hA (by positivity) hrj hQj
  have hpow : (2 : ℝ)^w.length ≤ (2 : ℝ)^N := pow_le_pow_right₀ (by norm_num) hw
  rw [haEq]
  calc
    _ ≤ (2 : ℝ)^w.length*A*(2*M) := h
    _ ≤ (2 : ℝ)^N*A*(2*M) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hA) (by positivity)
    _ = _ := by dsimp [A,r,beta,normalizedPrincipalCoordinateJetConstant]; rw [pow_succ]; ring

/-- Every ordinary derivative of the whole actual density-weighted principal
entry is retained before the native scalar formal adjoint is differentiated. -/
theorem abs_weightedActualNormalizedPrincipal_coordinate_word_le
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (x : R3) (eps M Cr : ℝ) (N : ℕ) (hN : N ≤ 8)
    (hδ : 0 < δ) (hR : 0 < R) (heps : 0 ≤ eps) (hM : 1 ≤ M) (hCr : 0 ≤ Cr)
    (hsmall : eps*referenceRadius δ R p L x ≤ 1)
    (hbeta : 1 ≤ actualReferenceBeta g1 L lam δ R p x)
    (hgeom : MixedPrincipalDensityBackgroundJetBound g1 L lam x M N)
    (hRadius : ActualRadiusCoordinateJetBound g1 L lam δ R p x Cr N)
    (hH8 : coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
      eps*referenceRadius δ R p L x)
    (w : List (Fin 3)) (hw : w.length ≤ N) (i j : Fin 3) :
    |coordinateFieldWordPartial w
      (fun y => referenceDensityFamily g1 L (lam,y)*
        actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam) y i j) x| ≤
      weightedNormalizedPrincipalCoordinateJetConstant N*Cr*M^2*referenceRadius δ R p L x*
        (actualReferenceBeta g1 L lam δ R p x)^w.length := by
  let mu : R3 → ℝ := fun y => referenceDensityFamily g1 L (lam,y)
  let a : R3 → ℝ := fun y => actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam) y i j
  let r : ℝ := referenceRadius δ R p L x
  let beta : ℝ := actualReferenceBeta g1 L lam δ R p x
  let A : ℝ := normalizedPrincipalCoordinateJetConstant N*Cr*M*r*beta^w.length
  have hr : 0 < r := referenceRadius_pos δ R p L x hδ hR
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hb0 : 0 ≤ beta := le_trans zero_le_one hbeta
  have hA : 0 ≤ A := by dsimp [A,normalizedPrincipalCoordinateJetConstant]; positivity
  have hm : ContDiff ℝ ∞ mu := by
    have hs : ContDiff ℝ ∞ (fun y : R3 => (lam,y)) :=
      (contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => lam)).prodMk
        (contDiff_id : ContDiff ℝ ∞ (fun y : R3 => y))
    simpa only [Function.comp_def] using (contDiff_referenceDensityFamily g1 hg1 L).comp hs
  have ha : ContDiff ℝ ∞ a := by
    have he : a=fun y => referenceRadius δ R p L y*referenceNormalizedPrincipalMatrix g1 g2 L lam y i j := by
      funext y
      dsimp only [a]
      rw [actualPrincipalMatrix_normalized_eq]
      rfl
    rw [he]
    exact contDiff_referenceRadius_mul_referenceNormalizedPrincipalMatrix_entry
      g1 g2 hg1 hg2 L lam δ R p hδ hR i j
  have haj (v : List (Fin 3)) (hv : v.length ≤ w.length) : |coordinateFieldWordPartial v a x| ≤ A := by
    have h := abs_actualNormalizedPrincipal_coordinate_word_le g1 g2 hg1 hg2 L lam δ R p x
      eps M Cr N hN hδ hR heps hM hCr hsmall hbeta hgeom hRadius hH8 v (le_trans hv hw) i j
    have hpow : beta^v.length ≤ beta^w.length := pow_le_pow_right₀ hbeta hv
    exact h.trans (mul_le_mul_of_nonneg_left hpow (by dsimp [normalizedPrincipalCoordinateJetConstant]; positivity))
  have h := abs_coordinateFieldWordPartial_mul_le w mu a hm ha x M A hM0 hA
    (fun v hv => hgeom.1.2.2.1 v (le_trans hv hw)) haj
  have hpow : (2 : ℝ)^w.length ≤ (2 : ℝ)^N := pow_le_pow_right₀ (by norm_num) hw
  change |coordinateFieldWordPartial w (fun y => mu y*a y) x| ≤ _
  calc
    _ ≤ (2 : ℝ)^w.length*M*A := h
    _ ≤ (2 : ℝ)^N*M*A := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hM0) hA
    _ = _ := by dsimp [A,r,beta,weightedNormalizedPrincipalCoordinateJetConstant]; ring

/-- Literal true scalar first-adjoint coefficient jets with all density
derivatives and the native ordinary-coordinate convention retained. -/
theorem abs_actualScalarAdjointFirst_coordinate_word_le
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (x : R3) (eps M Cr : ℝ) (N : ℕ) (hN : N+1 ≤ 8)
    (hδ : 0 < δ) (hR : 0 < R) (heps : 0 ≤ eps) (hM : 1 ≤ M) (hCr : 0 ≤ Cr)
    (hsmall : eps*referenceRadius δ R p L x ≤ 1)
    (hbeta : 1 ≤ actualReferenceBeta g1 L lam δ R p x)
    (hgeom : MixedPrincipalDensityBackgroundJetBound g1 L lam x M (N+1))
    (hRadius : ActualRadiusCoordinateJetBound g1 L lam δ R p x Cr (N+1))
    (hH8 : coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
      eps*referenceRadius δ R p L x)
    (w : List (Fin 3)) (hw : w.length ≤ N) (i : Fin 3) :
    |coordinateFieldWordPartial w
      (fun y => adjointFirstCoefficient coordinateDirection (fun z => referenceDensityFamily g1 L (lam,z))
        (actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam)) y i) x| ≤
      scalarAdjointFirstCoordinateJetConstant N*Cr*M^3*referenceRadius δ R p L x*
        (actualReferenceBeta g1 L lam δ R p x)^(w.length+1) := by
  let mu : R3 → ℝ := fun y => referenceDensityFamily g1 L (lam,y)
  let mui : R3 → ℝ := fun y => (mu y)⁻¹
  let a : Fin 3 → R3 → ℝ := fun j y => actualPrincipalMatrix g1 L lam δ R p
    (referenceNormalizedPrincipalDifference g1 g2 L lam) y i j
  let f : Fin 3 → R3 → ℝ := fun j y => mu y*a j y
  let d : Fin 3 → R3 → ℝ := fun j => directionalFDeriv (coordinateDirection j) (f j)
  let q : Fin 3 → R3 → ℝ := fun j y => mui y*d j y
  let r : ℝ := referenceRadius δ R p L x
  let beta : ℝ := actualReferenceBeta g1 L lam δ R p x
  let B : ℝ := weightedNormalizedPrincipalCoordinateJetConstant (N+1)*Cr*M^2*r*beta^(w.length+1)
  have hr : 0 < r := referenceRadius_pos δ R p L x hδ hR
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hb0 : 0 ≤ beta := le_trans zero_le_one hbeta
  have hB : 0 ≤ B := by dsimp [B,weightedNormalizedPrincipalCoordinateJetConstant,normalizedPrincipalCoordinateJetConstant]; positivity
  have hm : ContDiff ℝ ∞ mu := by
    have hs : ContDiff ℝ ∞ (fun y : R3 => (lam,y)) :=
      (contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => lam)).prodMk
        (contDiff_id : ContDiff ℝ ∞ (fun y : R3 => y))
    simpa only [Function.comp_def] using (contDiff_referenceDensityFamily g1 hg1 L).comp hs
  have hmi : ContDiff ℝ ∞ mui := by
    have hs : ContDiff ℝ ∞ (fun y : R3 => (lam,y)) :=
      (contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => lam)).prodMk
        (contDiff_id : ContDiff ℝ ∞ (fun y : R3 => y))
    simpa only [Function.comp_def] using (contDiff_referenceDensityFamily_inv g1 hg1 L).comp hs
  have ha (j : Fin 3) : ContDiff ℝ ∞ (a j) := by
    have he : a j=fun y => referenceRadius δ R p L y*referenceNormalizedPrincipalMatrix g1 g2 L lam y i j := by
      funext y
      dsimp only [a]
      rw [actualPrincipalMatrix_normalized_eq]
      rfl
    rw [he]
    exact contDiff_referenceRadius_mul_referenceNormalizedPrincipalMatrix_entry
      g1 g2 hg1 hg2 L lam δ R p hδ hR i j
  have hf (j : Fin 3) : ContDiff ℝ ∞ (f j) := hm.mul (ha j)
  have hd (j : Fin 3) : ContDiff ℝ ∞ (d j) := contDiff_directionalFDeriv (E := ℝ) (coordinateDirection j) _ (hf j)
  have hq (j : Fin 3) : ContDiff ℝ ∞ (q j) := hmi.mul (hd j)
  have hfj (j : Fin 3) (v : List (Fin 3)) (hv : v.length ≤ w.length+1) :
      |coordinateFieldWordPartial v (f j) x| ≤ B := by
    have h := abs_weightedActualNormalizedPrincipal_coordinate_word_le g1 g2 hg1 hg2 L lam δ R p x
      eps M Cr (N+1) hN hδ hR heps hM hCr hsmall hbeta hgeom hRadius hH8 v (by omega) i j
    have hpow : beta^v.length ≤ beta^(w.length+1) := pow_le_pow_right₀ hbeta hv
    exact h.trans (mul_le_mul_of_nonneg_left hpow
      (by dsimp [weightedNormalizedPrincipalCoordinateJetConstant,normalizedPrincipalCoordinateJetConstant]; positivity))
  have hdj (j : Fin 3) (v : List (Fin 3)) (hv : v.length ≤ w.length) : |coordinateFieldWordPartial v (d j) x| ≤ B := by
    have h := hfj j (v++[j]) (by simp only [List.length_append,List.length_singleton]; omega)
    simpa only [coordinateFieldWordPartial_append,coordinateFieldWordPartial,d] using h
  have hqj (j : Fin 3) : |coordinateFieldWordPartial w (q j) x| ≤ (2 : ℝ)^N*M*B := by
    have h := abs_coordinateFieldWordPartial_mul_le w mui (d j) hmi (hd j) x M B hM0 hB
      (fun v hv => hgeom.1.2.2.2 v (by omega)) (hdj j)
    have hpow : (2 : ℝ)^w.length ≤ (2 : ℝ)^N := pow_le_pow_right₀ (by norm_num) hw
    exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hM0) hB)
  have hAlpha : (fun y => adjointFirstCoefficient coordinateDirection mu
      (actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam)) y i) =
      fun y => 2*(∑ j : Fin 3, q j y) := by
    funext y
    dsimp [adjointFirstCoefficient,q,mui,d,f,a]
    simp only [Finset.mul_sum,mul_assoc]
  change |coordinateFieldWordPartial w
    (fun y => adjointFirstCoefficient coordinateDirection mu
      (actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam)) y i) x| ≤ _
  rw [hAlpha,coordinateFieldWordPartial_const_mul w 2 _ (ContDiff.sum (fun j _ => hq j)),
    coordinateFieldWordPartial_sum w q hq,abs_mul,show |(2 : ℝ)|=2 by norm_num]
  calc
    _ ≤ 2*∑ j : Fin 3, |coordinateFieldWordPartial w (q j) x| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ ≤ 2*∑ j : Fin 3, (2 : ℝ)^N*M*B := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hqj j)) (by norm_num)
    _ = _ := by simp only [Fin.sum_univ_three]; dsimp [B,r,beta,scalarAdjointFirstCoordinateJetConstant]; ring

/-- Literal true scalar zero-adjoint coefficient jets; native order is
partial_j partial_i of the whole mu*a_ij, with N+2<=8 paid by source H8. -/
theorem abs_actualScalarAdjointZero_coordinate_word_le
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (x : R3) (eps M Cr : ℝ) (N : ℕ) (hN : N+2 ≤ 8)
    (hδ : 0 < δ) (hR : 0 < R) (heps : 0 ≤ eps) (hM : 1 ≤ M) (hCr : 0 ≤ Cr)
    (hsmall : eps*referenceRadius δ R p L x ≤ 1)
    (hbeta : 1 ≤ actualReferenceBeta g1 L lam δ R p x)
    (hgeom : MixedPrincipalDensityBackgroundJetBound g1 L lam x M (N+2))
    (hRadius : ActualRadiusCoordinateJetBound g1 L lam δ R p x Cr (N+2))
    (hH8 : coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
      eps*referenceRadius δ R p L x)
    (w : List (Fin 3)) (hw : w.length ≤ N) :
    |coordinateFieldWordPartial w
      (fun y => adjointZeroCoefficient coordinateDirection (fun z => referenceDensityFamily g1 L (lam,z))
        (actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam)) y) x| ≤
      scalarAdjointZeroCoordinateJetConstant N*Cr*M^3*referenceRadius δ R p L x*
        (actualReferenceBeta g1 L lam δ R p x)^(w.length+2) := by
  let mu : R3 → ℝ := fun y => referenceDensityFamily g1 L (lam,y)
  let mui : R3 → ℝ := fun y => (mu y)⁻¹
  let a : Fin 3 → Fin 3 → R3 → ℝ := fun i j y => actualPrincipalMatrix g1 L lam δ R p
    (referenceNormalizedPrincipalDifference g1 g2 L lam) y i j
  let f : Fin 3 → Fin 3 → R3 → ℝ := fun i j y => mu y*a i j y
  let d : Fin 3 → Fin 3 → R3 → ℝ := fun i j => directionalFDeriv (coordinateDirection j)
    (directionalFDeriv (coordinateDirection i) (f i j))
  let q : Fin 3 → Fin 3 → R3 → ℝ := fun i j y => mui y*d i j y
  let r : ℝ := referenceRadius δ R p L x
  let beta : ℝ := actualReferenceBeta g1 L lam δ R p x
  let B : ℝ := weightedNormalizedPrincipalCoordinateJetConstant (N+2)*Cr*M^2*r*beta^(w.length+2)
  have hr : 0 < r := referenceRadius_pos δ R p L x hδ hR
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hb0 : 0 ≤ beta := le_trans zero_le_one hbeta
  have hB : 0 ≤ B := by dsimp [B,weightedNormalizedPrincipalCoordinateJetConstant,normalizedPrincipalCoordinateJetConstant]; positivity
  have hm : ContDiff ℝ ∞ mu := by
    have hs : ContDiff ℝ ∞ (fun y : R3 => (lam,y)) :=
      (contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => lam)).prodMk
        (contDiff_id : ContDiff ℝ ∞ (fun y : R3 => y))
    simpa only [Function.comp_def] using (contDiff_referenceDensityFamily g1 hg1 L).comp hs
  have hmi : ContDiff ℝ ∞ mui := by
    have hs : ContDiff ℝ ∞ (fun y : R3 => (lam,y)) :=
      (contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => lam)).prodMk
        (contDiff_id : ContDiff ℝ ∞ (fun y : R3 => y))
    simpa only [Function.comp_def] using (contDiff_referenceDensityFamily_inv g1 hg1 L).comp hs
  have ha (i j : Fin 3) : ContDiff ℝ ∞ (a i j) := by
    have he : a i j=fun y => referenceRadius δ R p L y*referenceNormalizedPrincipalMatrix g1 g2 L lam y i j := by
      funext y
      dsimp only [a]
      rw [actualPrincipalMatrix_normalized_eq]
      rfl
    rw [he]
    exact contDiff_referenceRadius_mul_referenceNormalizedPrincipalMatrix_entry
      g1 g2 hg1 hg2 L lam δ R p hδ hR i j
  have hf (i j : Fin 3) : ContDiff ℝ ∞ (f i j) := hm.mul (ha i j)
  have hd (i j : Fin 3) : ContDiff ℝ ∞ (d i j) := contDiff_directionalFDeriv (E := ℝ) (coordinateDirection j) _
    (contDiff_directionalFDeriv (E := ℝ) (coordinateDirection i) _ (hf i j))
  have hq (i j : Fin 3) : ContDiff ℝ ∞ (q i j) := hmi.mul (hd i j)
  have hfj (i j : Fin 3) (v : List (Fin 3)) (hv : v.length ≤ w.length+2) :
      |coordinateFieldWordPartial v (f i j) x| ≤ B := by
    have h := abs_weightedActualNormalizedPrincipal_coordinate_word_le g1 g2 hg1 hg2 L lam δ R p x
      eps M Cr (N+2) hN hδ hR heps hM hCr hsmall hbeta hgeom hRadius hH8 v (by omega) i j
    have hpow : beta^v.length ≤ beta^(w.length+2) := pow_le_pow_right₀ hbeta hv
    exact h.trans (mul_le_mul_of_nonneg_left hpow
      (by dsimp [weightedNormalizedPrincipalCoordinateJetConstant,normalizedPrincipalCoordinateJetConstant]; positivity))
  have hdj (i j : Fin 3) (v : List (Fin 3)) (hv : v.length ≤ w.length) : |coordinateFieldWordPartial v (d i j) x| ≤ B := by
    have h := hfj i j (v++[j,i]) (by simp only [List.length_append,List.length_cons,List.length_nil]; omega)
    simpa only [coordinateFieldWordPartial_append,coordinateFieldWordPartial,d] using h
  have hqj (i j : Fin 3) : |coordinateFieldWordPartial w (q i j) x| ≤ (2 : ℝ)^N*M*B := by
    have h := abs_coordinateFieldWordPartial_mul_le w mui (d i j) hmi (hd i j) x M B hM0 hB
      (fun v hv => hgeom.1.2.2.2 v (by omega)) (hdj i j)
    have hpow : (2 : ℝ)^w.length ≤ (2 : ℝ)^N := pow_le_pow_right₀ (by norm_num) hw
    exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hM0) hB)
  have hAlpha : (fun y => adjointZeroCoefficient coordinateDirection mu
      (actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam)) y) =
      fun y => ∑ i : Fin 3, ∑ j : Fin 3, q i j y := by
    funext y
    dsimp [adjointZeroCoefficient,q,mui,d,f,a]
    simp only [Finset.mul_sum]
  have hInner (i : Fin 3) : coordinateFieldWordPartial w (fun y => ∑ j : Fin 3, q i j y) =
      fun y => ∑ j : Fin 3, coordinateFieldWordPartial w (q i j) y :=
    coordinateFieldWordPartial_sum w (q i) (hq i)
  change |coordinateFieldWordPartial w
    (fun y => adjointZeroCoefficient coordinateDirection mu
      (actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam)) y) x| ≤ _
  rw [hAlpha,coordinateFieldWordPartial_sum w (fun i y => ∑ j : Fin 3, q i j y)
    (fun i => ContDiff.sum (fun j _ => hq i j))]
  simp_rw [hInner]
  calc
    _ ≤ ∑ i : Fin 3, |∑ j : Fin 3, coordinateFieldWordPartial w (q i j) x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, |coordinateFieldWordPartial w (q i j) x| :=
      Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, (2 : ℝ)^N*M*B :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hqj i j))
    _ = _ := by simp only [Fin.sum_univ_three]; dsimp [B,r,beta,scalarAdjointZeroCoordinateJetConstant]; ring

end OAI.AnisotropicCalderon.ActualNormalizedPrincipalDensityCoefficientJets
