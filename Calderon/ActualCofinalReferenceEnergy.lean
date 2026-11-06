import Calderon.ActualCofinalReferenceProfileBounds
import Calderon.ActualReferenceEnergyBetaThresholdCoercivity

/-! The original finite-mode → projected → all-mode → finite-core native T-gap argument, rerun
with the conformal parameter, degree and amplitude retained: every `L ≥ L0`, every `p ≥ p0` and
every positive amplitude (the smallness clauses for every `R ≤ R0`). No physical E/F, drift,
density or Main claim. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter

section Projected
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualCofinalReferenceCoercivity
open SphereHarmonic SpectralCoreRegularity SmoothSphereFields
  AmbientReferenceRaising HarmonicRaisingModel ReferenceDensityBounds
  CovariantHarmonicEnergy FischerConnectionTransport FiniteProfileNormComparison
  ActualReferenceProjectedEnergies ActualReferenceCoercivityBetaThreshold
  ActualHorizontalNormBridge ReferenceWeightedApproximation
  ActualNormalizedSecondDriftNativeAdjunction SmoothMetricFrame RadiusProfile ConformalDepth
  ActualReferenceProjectedCoercivityBetaThreshold

/-- Fixed conformal parameter: one coercivity constant, then for every floor one degree threshold,
and projected-mode coercivity for every larger degree and every positive amplitude. -/
theorem exists_referenceProjected_coercivity_forall_degree_ge
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K)
    (L c0 nu J1 J2 D : ℝ) (hL : 0 < L) (hc0 : 0 < c0) (hnu : 0 < nu)
    (hbounds : referenceProfileBounds g K L c0 nu J1 J2 D) :
    ∃ cRaise : ℝ, 0 < cRaise ∧ ∀ betaMin : ℝ, ∃ p0 : ℕ, 2 ≤ p0 ∧ ∀ p : ℕ, p0 ≤ p →
      (∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ x ∈ K,
        max (1:ℝ) betaMin ≤ referenceProfileNorm g lam δ R p L x) ∧
      ∀ hF : SphereFischerInner, ∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        ∀ R : ℝ, 0 < R → ∀ m : ℕ, ∀ G : R3 × R3 → ℝ, ∀ hG : ContDiff ℝ ∞ G,
        (∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) →
        cRaise * referenceHarmonicModeEnergy g lam δ R L p (m+1)
          (fun y => sphereHarmonicCoordinate hO hD (m+1) (ambientSphereL2 G hG y)) ≤
          referenceProjectedRaisingEnergy hF hO hD g hg L lam
            (referenceLogRadius δ R p L) G hG m -
          referenceProjectedLoweringEnergy hF hO hD g hg L lam
            (referenceLogRadius δ R p L) G hG m := by
  obtain ⟨C, hC, hcurv⟩ :=
    FiniteProfileRaisingGain.exists_referenceIntegratedCurvature_allFinite_uniform_bound.{0}
      g hg L hL K hK
  let a := min (1:ℝ) (nu/8)
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have hasmall : a ≤ nu/8 := min_le_right _ _
  have ha1 : a ≤ 1 := min_le_left _ _
  refine ⟨referenceProfileCoercivityConstant a nu,
    referenceProfileCoercivityConstant_pos a nu ha hnu, ?_⟩
  intro betaMin
  obtain ⟨p0, hp0, hfloor⟩ := referenceProfileBounds_exists_degree_floor
    g K L c0 nu J1 J2 D hc0 hbounds (max betaMin (50*C/nu))
  refine ⟨p0, hp0, ?_⟩
  intro p hp
  have hp1 : 1 ≤ p := le_trans (by norm_num) (hp0.trans hp)
  let beta0 := max (1:ℝ) (max betaMin (50*C/nu))
  have hb0 : 1 ≤ beta0 := le_max_left _ _
  have hab : a ≤ beta0 := ha1.trans hb0
  have habsorb : 50*C ≤ nu*beta0 := by
    have hq : 50*C/nu ≤ beta0 :=
      (le_max_right betaMin (50*C/nu)).trans (le_max_right (1:ℝ) (max betaMin (50*C/nu)))
    rw [mul_comm nu beta0]
    exact (div_le_iff₀ hnu).mp hq
  have hfl : max (1:ℝ) betaMin ≤ beta0 :=
    max_le (le_max_left _ _) ((le_max_left betaMin (50*C/nu)).trans (le_max_right _ _))
  refine ⟨fun lam hlam δ hδ hδ1 R hR x hx =>
    hfl.trans (hfloor p hp lam hlam δ hδ hδ1 R hR x hx), ?_⟩
  intro hF lam hlam δ hδ hδ1 R hR m G hG hz
  have hbeta : ∀ x ∈ K, beta0 ≤ referenceProfileNorm g lam δ R p L x :=
    fun x hx => hfloor p hp lam hlam δ hδ hδ1 R hR x hx
  let U : R3 → SphereL2 := ambientSphereL2 G hG
  have hU : ContDiff ℝ ∞ U := contDiff_ambientSphereL2 G hG
  have hzU : ∀ x ∉ K, U x = 0 := fun x hx => ambientSphereL2_eq_zero G hG x (hz x hx)
  obtain ⟨n,b,c,hb,hc,hcompact,hrep,hcz⟩ :=
    exists_smooth_compact_coordinates_sphereHarmonicCoordinate hO hD (m+1) U hU K hK hzU
  have hpoly : ∀ x ∉ K, finitePolynomialField b c x = 0 := by
    intro x hx
    simp only [finitePolynomialField,hcz x hx,Pi.zero_apply,zero_smul,Finset.sum_const_zero]
  have hproj := contDiff_sphereHarmonicCoordinate hO hD (m+1) U hU
  have hmodeE := referenceHarmonicModeEnergy_eq_polynomial g hg lam δ R L p (m+1)
    b hb c _ hc hproj hrep
  have hraise := referenceHarmonicRaisingEnergy_eq_polynomial hF g hg L lam m
    b hb c _ hc hproj hrep (referenceLogRadius δ R p L)
  have hlower := referenceHarmonicLoweringEnergy_eq_polynomial hF g hg L lam m
    b hb c _ hc hproj hrep (referenceLogRadius δ R p L)
  have hhcurv := hcurv (Fin n) hF lam hlam (m+1) (by omega) b hb c hc hcompact hpoly
  rw [Nat.cast_add, Nat.cast_one] at hhcurv
  have hh := referenceProfileModeEnergy_coercive hF g hg K hK.isClosed L c0 nu J1 J2 D hL hnu
    hbounds lam hlam δ hδ hδ1 R hR p hp1 m b hb c hc hcompact hpoly a beta0 C ha hb0 hC.le
    hasmall hab habsorb hbeta hhcurv
  rw [referenceProjectedRaisingEnergy_eq_harmonic,
    referenceProjectedLoweringEnergy_eq_harmonic]
  change referenceProfileCoercivityConstant a nu *
    referenceHarmonicModeEnergy g lam δ R L p (m+1)
      (fun y => sphereHarmonicCoordinate hO hD (m+1) (U y)) ≤
    referenceHarmonicRaisingEnergy hF g L lam m
      (fun y => sphereHarmonicCoordinate hO hD (m+1) (U y)) (referenceLogRadius δ R p L) -
    referenceHarmonicLoweringEnergy hF g L lam m
      (fun y => sphereHarmonicCoordinate hO hD (m+1) (U y)) (referenceLogRadius δ R p L)
  rw [hmodeE,hraise,hlower]
  exact hh

end OAI.AnisotropicCalderon.ActualCofinalReferenceCoercivity
end Projected

section AllMode
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualCofinalReferenceCoercivity
open SphereHarmonic SpectralCoreRegularity SmoothSphereFields
  AmbientReferenceRaising HarmonicRaisingModel ReferenceDensityBounds
  CovariantHarmonicEnergy ActualReferenceProjectedEnergies
  ActualReferenceProjectedCoercivityBetaThreshold AmbientReferenceCoercivity
  AmbientReferenceProfileEnergy ActualHorizontalNormBridge
  ReferenceWeightedApproximation ActualNormalizedSecondDriftNativeAdjunction
  SmoothMetricFrame RadiusProfile ConformalDepth ActualReferenceAllModeCoercivityBetaThreshold

/-- Fixed conformal parameter: all-mode raising gain for every degree above the threshold and
every positive amplitude, by summing the projected modes and passing to the cut limit. -/
theorem exists_referenceAllMode_coercivity_forall_degree_ge
    (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K)
    (L c0 nu J1 J2 D : ℝ) (hL : 0 < L) (hc0 : 0 < c0) (hnu : 0 < nu)
    (hbounds : referenceProfileBounds g K L c0 nu J1 J2 D) :
    ∃ cRaise : ℝ, 0 < cRaise ∧ ∀ betaMin : ℝ, ∃ p0 : ℕ, 2 ≤ p0 ∧ ∀ p : ℕ, p0 ≤ p →
      (∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ x ∈ K,
        max (1:ℝ) betaMin ≤ referenceProfileNorm g lam δ R p L x) ∧
      ∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R →
        ∀ G : R3 × R3 → ℝ, ∀ hG : ContDiff ℝ ∞ G,
        (∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) →
        (∀ x, sphereMean (ambientSphereL2 G hG x)=0) →
        cRaise * referenceAllModeProfileEnergy hO hD g hg lam δ R L p G hG ≤
          referenceAllModeRaisingEnergy hF hO hD g hg L lam
            (referenceLogRadius δ R p L) G hG -
          referenceAllModeLoweringEnergy hF hO hD g hg L lam
            (referenceLogRadius δ R p L) G hG := by
  obtain ⟨cRaise, hcRaise, hprofile⟩ := exists_referenceProjected_coercivity_forall_degree_ge
    hO hD g hg K hK L c0 nu J1 J2 D hL hc0 hnu hbounds
  refine ⟨cRaise, hcRaise, ?_⟩
  intro betaMin
  obtain ⟨p0, hp0, hdeg⟩ := hprofile betaMin
  refine ⟨p0, hp0, ?_⟩
  intro p hp
  obtain ⟨hfloor, hmode⟩ := hdeg p hp
  have hp1 : 1 ≤ p := le_trans (by norm_num) (hp0.trans hp)
  refine ⟨hfloor, ?_⟩
  intro lam hlam δ hδ hδ1 R hR G hG hz hmean
  have hfinite (n : ℕ) :
      cRaise * referenceAllModeProfileCutEnergy hO hD g hg lam δ R L p n G hG ≤
        referenceAllModeRaisingCutEnergy hF hO hD g hg L lam
          (referenceLogRadius δ R p L) n G hG -
        referenceAllModeLoweringCutEnergy hF hO hD g hg L lam
          (referenceLogRadius δ R p L) n G hG := by
    rw [referenceAllModeProfileCutEnergy_eq_sum_modes hF hO hD g hg lam δ R L p n
        hδ hR hL hp1 G hG K hK hz,
      referenceAllModeRaisingCutEnergy_eq_sum_modes hF hO hD g hg lam δ R L p n
        hδ hR hL hp1 G hG K hK hz,
      referenceAllModeLoweringCutEnergy_eq_sum_modes hF hO hD g hg lam δ R L p n
        hδ hR hL hp1 G hG K hK hz,
      Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro m _
    simpa only [referenceProjectedRaisingEnergy_eq_harmonic,
      referenceProjectedLoweringEnergy_eq_harmonic] using
      hmode hF lam hlam δ hδ hδ1 R hR m G hG hz
  have hf := contDiff_log_referenceRadius δ R p L hδ hR
  exact le_of_tendsto_of_tendsto
    ((tendsto_referenceAllModeProfileCutEnergy hO hD g hg lam δ R L p hδ hR hL
      hp1 G hG K hK hz hmean).const_mul cRaise)
    ((tendsto_referenceAllModeRaisingCutEnergy hF hO hD g hg L lam _ hf G hG K hK hz hmean).sub
      (tendsto_referenceAllModeLoweringCutEnergy hF hO hD g hg L lam _ hf G hG K hK hz))
    (Filter.Eventually.of_forall hfinite)

end OAI.AnisotropicCalderon.ActualCofinalReferenceCoercivity
end AllMode

section FiniteCore
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicAmbient SpectralWeightedGraph
  SmoothSphereFields AmbientReferenceCoercivity AmbientReferenceProfileEnergy ReferenceDensityBounds
  ReferenceWeightedApproximation ConformalDepth ActualReferenceAllModeCoercivityBetaThreshold
  ActualCofinalReferenceCoercivity
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev cofinalEnergyFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) := ⟨fun F => F.val⟩
attribute [local instance] cofinalEnergyFunction

/-- Fixed conformal parameter: native finite-core T-gap for every degree above the threshold and
every positive amplitude, with the exact native `T`, `T†`, `Z`, density and actual beta. -/
theorem exists_nativeReference_energy_forall_degree_ge
    (hF : SphereFischerInner) (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (K : Set R3) (hK : IsCompact K)
    (L c0 nu J1 J2 D : ℝ) (hL : 0 < L) (hc0 : 0 < c0) (hnu : 0 < nu)
    (hbounds : referenceProfileBounds g1 K L c0 nu J1 J2 D) :
    ∃ cRaise : ℝ, 0 < cRaise ∧ ∀ betaMin : ℝ, ∃ p0 : ℕ, 2 ≤ p0 ∧ ∀ p : ℕ, p0 ≤ p →
      (∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ x ∈ K,
        max (1:ℝ) betaMin ≤ actualReferenceBeta g1 L lam δ R p x) ∧
      ∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 → ∀ R : ℝ, ∀ hR : 0 < R,
        ∀ F : smoothCompactFiniteSphereCore hO hD,
        tsupport (F : R3 → SphereL2) ⊆ K → (∀ x, sphereMean (F x)=0) →
        cRaise*(∫ x : R3, referenceDensityFamily g1 L (lam,x)*
          finiteCoreReferenceProfileEnergy hO hD g1 hg1 L lam
            (actualReferenceBeta g1 L lam δ R p x) F x) ≤
          (∫ x : R3, referenceDensityFamily g1 L (lam,x)*
            ‖nativeT hO hD hF g1 hg1 L lam δ R p hδ hR F x‖^2)-
          (∫ x : R3, referenceDensityFamily g1 L (lam,x)*
            ‖nativeTdag hO hD hF g1 hg1 L lam δ R p hδ hR F x+
              nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR F x‖^2) := by
  obtain ⟨c, hc, hgain⟩ := exists_referenceAllMode_coercivity_forall_degree_ge
    hF hO hD g1 hg1 K hK L c0 nu J1 J2 D hL hc0 hnu hbounds
  refine ⟨c, hc, ?_⟩
  intro betaMin
  obtain ⟨p0, hp0, hdeg⟩ := hgain betaMin
  refine ⟨p0, hp0, ?_⟩
  intro p hp
  obtain ⟨hfloor, hfields⟩ := hdeg p hp
  refine ⟨fun lam hlam δ hδ hδ1 R hR x hx => ?_, ?_⟩
  · rw [← referenceProfileNorm_eq_actualReferenceBeta]
    exact hfloor lam hlam δ hδ hδ1 R hR x hx
  intro lam hlam δ hδ hδ1 R hR F hsupp hmean
  let r := coreAmbientRepresentative hO hD F
  have hz (x : R3) (hx : x ∉ K) (theta : UnitSphere) :
      representativeAmbient hO hD r (x,theta.val)=0 :=
    representativeAmbient_zero_outside hO hD r x theta.val (fun hy => hx (hsupp hy))
  have hm (x : R3) : sphereMean (ambientSphereL2 (representativeAmbient hO hD r)
      (contDiff_representativeAmbient hO hD r) x)=0 := by
    rw [ambientSphereL2_representative hO hD r x]
    exact hmean x
  have ht := hfields lam hlam δ hδ hδ1 R hR (representativeAmbient hO hD r)
    (contDiff_representativeAmbient hO hD r) hz hm
  rw [referenceAllModeProfileEnergy_representative hO hD g1 hg1 lam δ R L p F r,
    referenceAllModeRaisingEnergy_representative hO hD hF g1 hg1 L lam δ R p hδ hR F r,
    referenceAllModeLoweringEnergy_representative hO hD hF g1 hg1 L lam δ R p hδ hR F r] at ht
  exact ht

/-- Cofinal native T-gap: `L0`, then every `L ≥ L0`, `cRaise`, every floor, `p0`, every
`p ≥ p0`, every `eps`, `R0`, every positive amplitude `R ≤ R0`, every `lam`, `δ` and finite
mean-zero core supported in `K`. The gap itself holds for every positive amplitude. -/
theorem exists_nativeReference_energy_cofinal_profile
    (hF : SphereFischerInner) (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (K : Set R3) (hK : IsCompact K) :
    ∃ L0 : ℝ, 0 < L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∃ cRaise : ℝ, 0 < cRaise ∧ ∀ betaMin : ℝ, ∃ p0 : ℕ, 2 ≤ p0 ∧ ∀ p : ℕ, p0 ≤ p →
        ∀ eps : ℝ, 0 < eps → ∃ R0 : ℝ, 0 < R0 ∧ ∀ R : ℝ, ∀ hR : 0 < R, R ≤ R0 →
          (∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x ∈ K,
            max (1:ℝ) betaMin ≤ actualReferenceBeta g1 L lam δ R p x ∧
            ‖fderiv ℝ (referenceRadius δ R p L) x‖ ≤ eps ∧
            referenceRadius δ R p L x*(actualReferenceBeta g1 L lam δ R p x)^2 ≤ eps) ∧
          ∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 →
            ∀ F : smoothCompactFiniteSphereCore hO hD,
            tsupport (F : R3 → SphereL2) ⊆ K → (∀ x, sphereMean (F x)=0) →
            cRaise*(∫ x : R3, referenceDensityFamily g1 L (lam,x)*
              finiteCoreReferenceProfileEnergy hO hD g1 hg1 L lam
                (actualReferenceBeta g1 L lam δ R p x) F x) ≤
              (∫ x : R3, referenceDensityFamily g1 L (lam,x)*
                ‖nativeT hO hD hF g1 hg1 L lam δ R p hδ hR F x‖^2)-
              (∫ x : R3, referenceDensityFamily g1 L (lam,x)*
                ‖nativeTdag hO hD hF g1 hg1 L lam δ R p hδ hR F x+
                  nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR F x‖^2) := by
  obtain ⟨L0, hL0, hprofile⟩ := exists_referenceProfileBounds_forall_ge g1 hg1 K hK
  refine ⟨L0, hL0, ?_⟩
  intro L hLge
  have hL : 0 < L := hL0.trans_le hLge
  obtain ⟨c0, nu, J1, J2, D, hc0, hnu, -, -, -, hbounds⟩ := hprofile L hLge
  obtain ⟨c, hc, hgain⟩ := exists_nativeReference_energy_forall_degree_ge
    hO hD hF g1 hg1 K hK L c0 nu J1 J2 D hL hc0 hnu hbounds
  refine ⟨c, hc, ?_⟩
  intro betaMin
  obtain ⟨p0, hp0, hdeg⟩ := hgain betaMin
  refine ⟨p0, hp0, ?_⟩
  intro p hp eps heps
  obtain ⟨hfloor, hgap⟩ := hdeg p hp
  obtain ⟨R0, hR0, hsmall⟩ := exists_referenceRadius_small_amplitude_forall_le
    g1 hg1 K hK L hL p (hp0.trans hp) eps heps
  refine ⟨R0, hR0, ?_⟩
  intro R hR hRR
  refine ⟨fun lam hlam δ hδ hδ1 x hx =>
    ⟨hfloor lam hlam δ hδ hδ1 R hR x hx, hsmall R hR hRR lam hlam δ hδ hδ1 x hx⟩, ?_⟩
  intro lam hlam δ hδ hδ1 F hsupp hmean
  exact hgap lam hlam δ hδ hδ1 R hR F hsupp hmean

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
end FiniteCore
