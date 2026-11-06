import Calderon.ActualNormalizedSecondDriftNativeAdjunction
import Calderon.ActualNormalizedSecondDriftWeightedCoefficients

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualNormalizedSecondDriftDefectWeightedJets
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  SmoothSphereFields SmoothAngularApplication SmoothMetricFrame MovingFrameConnection
  ActualNormalizedSecondMetricDrift ActualNormalizedSecondDriftAngularAllocation
  ActualNormalizedSecondDriftNativeAdjunction ActualNormalizedSecondDriftWeightedCoefficients
  ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherHCoframeJets
  ActualReferenceDDHigherProfileJets ActualReferenceDDHigherCLMProducts
  ActualScalarPrincipalAdjoint ReferenceDensityBounds PrincipalCommutator ConformalDepth RadiusProfile

/- Actual differentiated density coefficient of native rb2 only. -/

def referenceDensityLogCoordinateJoint (g : MatrixField) (L : ℝ) (j : Fin 3) (z : ℝ × R3) : ℝ :=
  (referenceDensityFamily g L z)⁻¹ * familyDirectionalDeriv j (referenceDensityFamily g L) z

lemma contDiff_referenceDensityLogCoordinateJoint (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (j : Fin 3) :
  ContDiff ℝ ∞ (referenceDensityLogCoordinateJoint g L j) := by
  unfold referenceDensityLogCoordinateJoint
  exact (contDiff_referenceDensityFamily_inv g hg L).mul
    (contDiff_familyDirectionalDeriv j (referenceDensityFamily g L)
      (contDiff_referenceDensityFamily g hg L))


lemma referenceDensityLogCoordinateJoint_eq_slice (g : MatrixField) (L lam : ℝ) (j : Fin 3) (x : R3) :
  referenceDensityLogCoordinateJoint g L j (lam,x) =
    (referenceDensityFamily g L (lam,x))⁻¹ *
      directionalFDeriv (coordinateDirection j) (fun y => referenceDensityFamily g L (lam,y)) x := by
  rfl


theorem normalizedSecondDriftDensityDivergence_coordinate_expansion (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (x : R3) :
  normalizedSecondDriftDensityDivergence g1 g2 L lam δ R p x =
    ∑ j : Fin 3,
      (directionalFDeriv (coordinateDirection j)
        (fun y => referenceRadius δ R p L y * normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,y)) x +
      referenceDensityLogCoordinateJoint g1 L j (lam,x) *
        (referenceRadius δ R p L x * normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,x))) := by
  let mu (y : R3) : ℝ := referenceDensityFamily g1 L (lam,y)
  let a (j : Fin 3) (y : R3) : ℝ := referenceRadius δ R p L y *
    normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,y)
  have hm : ContDiff ℝ ∞ mu :=
    (contDiff_referenceDensityFamily g1 hg1 L).comp (contDiff_const.prodMk contDiff_id)
  have ha (j : Fin 3) : ContDiff ℝ ∞ (a j) :=
    (contDiff_referenceRadius_actual δ R p L hδ hR).mul
      ((contDiff_normalizedSecondDriftCoordinateJoint g1 g2 hg1 hg2 L j).comp
        (contDiff_const.prodMk contDiff_id))
  have hp (j : Fin 3) : directionalFDeriv (coordinateDirection j)
      (fun y => mu y*a j y) x =
      directionalFDeriv (coordinateDirection j) mu x*a j x +
        mu x*directionalFDeriv (coordinateDirection j) (a j) x := by
    simpa only [smul_eq_mul] using directionalFDeriv_smul (coordinateDirection j) mu (a j)
      hm (ha j) x
  have hmu : mu x ≠ 0 := (referenceDensityFamily_pos g1 hg1 L (lam,x)).ne'
  unfold normalizedSecondDriftDensityDivergence
  simp only [mul_assoc]
  change (mu x)⁻¹ * (∑ j : Fin 3,
      directionalFDeriv (coordinateDirection j) (fun y => mu y*a j y) x) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hp,referenceDensityLogCoordinateJoint_eq_slice]
  change (mu x)⁻¹ * (directionalFDeriv (coordinateDirection j) mu x*a j x+
    mu x*directionalFDeriv (coordinateDirection j) (a j) x) =
    directionalFDeriv (coordinateDirection j) (a j) x+
      (mu x)⁻¹*directionalFDeriv (coordinateDirection j) mu x*a j x
  field_simp
  ring


theorem exists_referenceDensityLogCoordinate_uniform_coordinate_word_bounds (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (K : Set R3) (hK : IsCompact K) (N : ℕ) :
  ∃ M : ℝ, 1 ≤ M ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K,
    ∀ j : Fin 3, ∀ w : List (Fin 3), w.length ≤ N →
      ‖coordinateFieldWordPartial w (fun y => referenceDensityLogCoordinateJoint g L j (lam,y)) x‖ ≤ M := by
  exact exists_parameter_coordinate_word_uniform_bound
    (fun j : Fin 3 => referenceDensityLogCoordinateJoint g L j)
    (fun j => contDiff_referenceDensityLogCoordinateJoint g hg L j) K hK N


theorem exists_normalizedSecondDriftDensityDivergence_uniform_coordinate_word_jet_bound (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) (N : ℕ) :
  ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
    ∀ x ∈ K,
    let beta := metricDifferentialNorm (referenceMetric (dilatedMetric g1 lam) L)
      (fun y => Real.log (referenceRadius δ R p L y)) x;
    1 ≤ beta → HasCoordinateWordJetBound N
      (normalizedSecondDriftDensityDivergence g1 g2 L lam δ R p) x
      (C*referenceRadius δ R p L x) beta 1 := by
  obtain ⟨Mb,hMb,hb2⟩ := exists_normalizedSecondDrift_uniform_coordinate_word_bounds
    g1 g2 hg1 hg2 L K hK (N+1)
  obtain ⟨Mmu,hMmu,hlog⟩ := exists_referenceDensityLogCoordinate_uniform_coordinate_word_bounds
    g1 hg1 L K hK N
  obtain ⟨Cr,hCr,hradius⟩ := exists_referenceRadius_uniform_coordinate_word_bounds g1 hg1 L hL K hK (N+1)
  let A : ℝ := (2:ℝ)^(N+1)*Cr*Mb
  let T : ℝ := (2:ℝ)^N
  let C : ℝ := 3*A*(1+T*Mmu)
  have hMb0 : 0 ≤ Mb := by linarith
  have hMmu0 : 0 ≤ Mmu := by linarith
  have hA : 0 < A := by dsimp [A]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx beta hbeta
  have hb0 : 0 ≤ beta := by linarith
  let r0 : ℝ := referenceRadius δ R p L x
  have hr0 : 0 < r0 := referenceRadius_pos δ R p L x hδ hR
  let a (j : Fin 3) (y : R3) : ℝ := referenceRadius δ R p L y *
    normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,y)
  have hrS := contDiff_referenceRadius_actual δ R p L hδ hR
  have hbS (j : Fin 3) : ContDiff ℝ ∞
      (fun y : R3 => normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,y)) :=
    (contDiff_normalizedSecondDriftCoordinateJoint g1 g2 hg1 hg2 L j).comp
      (contDiff_const.prodMk contDiff_id)
  have haS (j : Fin 3) : ContDiff ℝ ∞ (a j) := hrS.mul (hbS j)
  have hLS (j : Fin 3) : ContDiff ℝ ∞
      (fun y : R3 => referenceDensityLogCoordinateJoint g1 L j (lam,y)) :=
    (contDiff_referenceDensityLogCoordinateJoint g1 hg1 L j).comp
      (contDiff_const.prodMk contDiff_id)
  have hrjet : HasCoordinateWordJetBound (N+1) (referenceRadius δ R p L) x (Cr*r0) beta 0 := by
    intro w hw
    simpa only [Real.norm_eq_abs,r0,Nat.zero_add,mul_assoc] using
      (hradius lam hlam δ hδ hδ1 R hR p hp x hx w hw).1
  have hbjet (j : Fin 3) : HasCoordinateWordJetBound (N+1)
      (fun y => normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,y)) x Mb beta 0 := by
    intro w hw
    have hword := (hb2 lam hlam x hx w hw).1 j
    have hpow : 1 ≤ beta^w.length := one_le_pow₀ hbeta
    have hconst : Mb ≤ Mb*beta^w.length := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hMb0
    simpa only [Real.norm_eq_abs,Nat.zero_add] using hword.trans hconst
  have hAjet (j : Fin 3) : HasCoordinateWordJetBound (N+1) (a j) x (A*r0) beta 0 := by
    have ht := hasCoordinateWordJetBound_mul (N+1) (referenceRadius δ R p L)
      (fun y => normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,y)) hrS (hbS j)
      x (Cr*r0) Mb beta 0 0 (mul_nonneg hCr.le hr0.le) hMb0 hb0 hrjet (hbjet j)
    have he : (2:ℝ)^(N+1)*(Cr*r0)*Mb=A*r0 := by dsimp [A]; ring
    rw [he] at ht
    exact ht
  have hDer (j : Fin 3) : HasCoordinateWordJetBound N
      (directionalFDeriv (coordinateDirection j) (a j)) x (A*r0) beta 1 :=
    hasCoordinateWordJetBound_coordinate_derivative N (a j) x (A*r0) beta 0 j (hAjet j)
  have hDerS (j : Fin 3) : ContDiff ℝ ∞
      (directionalFDeriv (coordinateDirection j) (a j)) :=
    ((haS j).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hLog (j : Fin 3) : HasCoordinateWordJetBound N
      (fun y => referenceDensityLogCoordinateJoint g1 L j (lam,y)) x Mmu beta 0 := by
    intro w hw
    have hword := hlog lam hlam x hx j w hw
    have hpow : 1 ≤ beta^w.length := one_le_pow₀ hbeta
    have hconst : Mmu ≤ Mmu*beta^w.length := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hMmu0
    simpa only [Nat.zero_add] using hword.trans hconst
  have hProduct (j : Fin 3) : HasCoordinateWordJetBound N
      (fun y => referenceDensityLogCoordinateJoint g1 L j (lam,y)*a j y)
      x (T*Mmu*A*r0) beta 1 := by
    have haN := hasCoordinateWordJetBound_truncate N (N+1) (a j) x (A*r0) beta 0
      (hAjet j) (by omega)
    have ht := hasCoordinateWordJetBound_mul N
      (fun y => referenceDensityLogCoordinateJoint g1 L j (lam,y)) (a j) (hLS j) (haS j)
      x Mmu (A*r0) beta 0 0 hMmu0 (mul_nonneg hA.le hr0.le) hb0 (hLog j) haN
    have he : (2:ℝ)^N*Mmu*(A*r0)=T*Mmu*A*r0 := by dsimp [T]; ring
    rw [he] at ht
    exact hasCoordinateWordJetBound_raise_degree N _ x (T*Mmu*A*r0) beta 0 1
      (by positivity) hbeta (by omega) ht
  have hTermS (j : Fin 3) : ContDiff ℝ ∞ (fun y : R3 =>
      directionalFDeriv (coordinateDirection j) (a j) y+
        referenceDensityLogCoordinateJoint g1 L j (lam,y)*a j y) :=
    (hDerS j).add ((hLS j).mul (haS j))
  have hTerm (j : Fin 3) : HasCoordinateWordJetBound N (fun y =>
      directionalFDeriv (coordinateDirection j) (a j) y+
        referenceDensityLogCoordinateJoint g1 L j (lam,y)*a j y)
      x ((A+T*Mmu*A)*r0) beta 1 := by
    have ht := hasCoordinateWordJetBound_add N _ _ (hDerS j) ((hLS j).mul (haS j))
      x (A*r0) (T*Mmu*A*r0) beta 1 (hDer j) (hProduct j)
    have he : A*r0+T*Mmu*A*r0=(A+T*Mmu*A)*r0 := by ring
    rwa [he] at ht
  have hSum := hasCoordinateWordJetBound_sum N (fun j : Fin 3 => fun y =>
    directionalFDeriv (coordinateDirection j) (a j) y+
      referenceDensityLogCoordinateJoint g1 L j (lam,y)*a j y)
    hTermS x ((A+T*Mmu*A)*r0) beta 1 hTerm
  have heC : (3:ℝ)*((A+T*Mmu*A)*r0)=C*r0 := by dsimp [C]; ring
  have he : normalizedSecondDriftDensityDivergence g1 g2 L lam δ R p =
      fun y => ∑ j : Fin 3, (directionalFDeriv (coordinateDirection j) (a j) y+
        referenceDensityLogCoordinateJoint g1 L j (lam,y)*a j y) := by
    funext y
    exact normalizedSecondDriftDensityDivergence_coordinate_expansion g1 g2 hg1 hg2 L lam δ R p hδ hR y
  rw [he]
  simpa only [Fintype.card_fin,Nat.cast_ofNat,heC] using hSum


theorem exists_normalizedSecondDriftDensityDivergence_uniform_coordinate_word_smallness (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) (N : ℕ) :
  ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
    ∀ eps : ℝ, 0 ≤ eps → ∀ x ∈ K,
    let beta := metricDifferentialNorm (referenceMetric (dilatedMetric g1 lam) L)
      (fun y => Real.log (referenceRadius δ R p L y)) x;
    1 ≤ beta → referenceRadius δ R p L x*beta^2 ≤ eps →
    ∀ w : List (Fin 3), w.length ≤ N →
      ‖coordinateFieldWordPartial w (normalizedSecondDriftDensityDivergence g1 g2 L lam δ R p) x‖ ≤
        (C*eps/beta)*beta^w.length := by
  obtain ⟨C,hC,hjet⟩ := exists_normalizedSecondDriftDensityDivergence_uniform_coordinate_word_jet_bound
    g1 g2 hg1 hg2 L hL K hK N
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps x hx beta hb hsmall w hw
  have hbpos : 0 < beta := by linarith
  have hb0 : 0 ≤ beta := hbpos.le
  have ht := hjet lam hlam δ hδ hδ1 R hR p hp x hx hb w hw
  have hs : C*referenceRadius δ R p L x*beta ≤ C*eps/beta := by
    apply (le_div_iff₀ hbpos).mpr
    calc
      C*referenceRadius δ R p L x*beta*beta = C*(referenceRadius δ R p L x*beta^2) := by ring
      _ ≤ C*eps := mul_le_mul_of_nonneg_left hsmall hC.le
  apply ht.trans
  calc
    (C*referenceRadius δ R p L x)*beta^(1+w.length) =
      (C*referenceRadius δ R p L x*beta)*beta^w.length := by rw [pow_add,pow_one]; ring
    _ ≤ (C*eps/beta)*beta^w.length := mul_le_mul_of_nonneg_right hs (pow_nonneg hb0 _)


end OAI.AnisotropicCalderon.ActualNormalizedSecondDriftDefectWeightedJets
