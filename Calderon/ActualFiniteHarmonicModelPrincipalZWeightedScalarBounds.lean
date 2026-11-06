import Calderon.ActualFiniteHarmonicModelPrincipalZScalarAction
import Calderon.ActualNormalizedPrincipalDensityCoefficientJets

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open ActualScalarPrincipalAdjoint ActualNormalizedSecondModelErrorAssembly
  NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth ReferenceDensityBounds PrincipalCommutator
  ActualMixedDensityScalarZeroForm ActualNormalizedPrincipalDensityCoefficientJets
  ActualReferenceDDHigherHCoframeJets ActualReferenceDDHigherGeometryJets
  ActualReferenceDDHigherLogFrameJets CoordinateBootstrapJets ReferenceWeightedApproximation
  ConformalDepth SmoothMetricFrame MovingFrameConnection AmbientReferenceRaising

theorem exists_nativePrincipalDefectWeightedScalar_uniform_bounds
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ x ∈ K,
      let beta := actualReferenceBeta g1 L lam δ R p x
      let mu : R3 → ℝ := fun y => referenceDensityFamily g1 L (lam,y)
      1 ≤ beta →
      coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius δ R p L x →
      referenceRadius δ R p L x * beta^2 ≤ eps →
      ∀ i j a : Fin 3,
      |mu x * nativePrincipalDefectScalarCoefficient g1 g2 L lam δ R p i j a x| ≤
        mu x * (C*eps/beta) ∧
      ∀ k : Fin 3,
        |directionalFDeriv (coordinateDirection k)
          (fun y => mu y * nativePrincipalDefectScalarCoefficient g1 g2 L lam δ R p i j a y) x| ≤
          mu x * (C*eps) := by
  obtain ⟨M,hM,hgeom⟩ := exists_mixed_principal_density_background_jet_bound g1 hg1 L K hK 1
  obtain ⟨Cr,hCr,hRadius⟩ := exists_actual_radius_coordinate_jet_bound g1 hg1 L hL K hK 1
  obtain ⟨J,hJ,hLog⟩ := exists_referenceDD_logRadius_frame_uniform_coordinate_word_bounds
    g1 hg1 L hL K hK 1
  let Cp : ℝ := weightedNormalizedPrincipalCoordinateJetConstant 1*Cr*M^2
  let D : ℝ := 2*Cp*J
  let C : ℝ := 1+M*D
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hCp : 0 < Cp := by
    dsimp only [Cp,weightedNormalizedPrincipalCoordinateJetConstant,normalizedPrincipalCoordinateJetConstant]
    positivity
  have hD : 0 < D := by dsimp only [D]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta mu hb hH8 hsmall i j a
  let r : ℝ := referenceRadius δ R p L x
  let Q : R3 → ℝ := fun y => mu y * actualPrincipalMatrix g1 L lam δ R p
    (referenceNormalizedPrincipalDifference g1 g2 L lam) y i j
  let f : R3 → ℝ := referenceFrameDerivative g1 L lam a
    (fun y => Real.log (referenceRadius δ R p L y))
  have hr : 0 < r := referenceRadius_pos δ R p L x hδ hR
  have hbpos : 0 < beta := lt_of_lt_of_le zero_lt_one hb
  have hb0 : 0 ≤ beta := hbpos.le
  change r*beta^2 ≤ eps at hsmall
  have hr1 : r ≤ 1 :=
    ((le_mul_of_one_le_right hr.le (one_le_pow₀ hb)).trans hsmall).trans heps1
  have hsm1 : eps*referenceRadius δ R p L x ≤ 1 := by change eps*r ≤ 1; nlinarith
  have hmu : 0 < mu x := referenceDensityFamily_pos g1 hg1 L (lam,x)
  have hInv : (mu x)⁻¹ ≤ M := by
    have ht := (hgeom lam hlam x hx).1.2.2.2 [] (by simp)
    simpa only [coordinateFieldWordPartial,abs_of_pos (inv_pos.mpr hmu),mu] using ht
  have hmuM : 1 ≤ mu x*M := by
    have ht := mul_le_mul_of_nonneg_left hInv hmu.le
    simpa only [mul_inv_cancel₀ hmu.ne'] using ht
  have hDC : D ≤ mu x*C := by
    calc
      D = 1*D := by ring
      _ ≤ (mu x*M)*D := mul_le_mul_of_nonneg_right hmuM hD.le
      _ = mu x*(M*D) := by ring
      _ ≤ mu x*C := mul_le_mul_of_nonneg_left (by dsimp only [C]; linarith) hmu.le
  have hQ (w : List (Fin 3)) (hw : w.length ≤ 1) :
      |coordinateFieldWordPartial w Q x| ≤ Cp*r*beta^w.length := by
    exact abs_weightedActualNormalizedPrincipal_coordinate_word_le g1 g2 hg1 hg2
      L lam δ R p x eps M Cr 1 (by norm_num) hδ hR heps hM hCr.le hsm1 hb
      (hgeom lam hlam x hx) (hRadius lam hlam δ hδ hδ1 R hR p hp x hx) hH8 w hw i j
  have hf (w : List (Fin 3)) (hw : w.length ≤ 1) :
      |coordinateFieldWordPartial w f x| ≤ J*beta^(1+w.length) := by
    exact (hLog lam hlam δ hδ hδ1 R hR p hp x hx hb w hw).1 a
  have hQ0 : |Q x| ≤ Cp*r := by simpa only [coordinateFieldWordPartial,List.length_nil,pow_zero,mul_one] using hQ [] (by simp)
  have hf0 : |f x| ≤ J*beta := by simpa only [coordinateFieldWordPartial,List.length_nil,Nat.add_zero,pow_one] using hf [] (by simp)
  have hQ1 (k : Fin 3) : |directionalFDeriv (coordinateDirection k) Q x| ≤ Cp*r*beta := by
    simpa only [coordinateFieldWordPartial,List.length_cons,List.length_nil,Nat.zero_add,pow_one] using hQ [k] (by simp)
  have hf1 (k : Fin 3) : |directionalFDeriv (coordinateDirection k) f x| ≤ J*beta^2 := by
    simpa only [coordinateFieldWordPartial,List.length_cons,List.length_nil] using hf [k] (by simp)
  have hmS : ContDiff ℝ ∞ mu :=
    (contDiff_referenceDensityFamily g1 hg1 L).comp (contDiff_const.prodMk contDiff_id)
  have hQS : ContDiff ℝ ∞ Q := hmS.mul
    (ActualPerturbedDefect.contDiff_actualPrincipalMatrix_entry g1 hg1 L lam δ R p
      (referenceNormalizedPrincipalDifference g1 g2 L lam) hδ hR
      (fun b c => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam b c) i j)
  have hfS : ContDiff ℝ ∞ f := contDiff_referenceFrameDerivative g1 hg1 L lam a _
    (contDiff_log_referenceRadius_profile δ R L p hδ hR)
  have he : (fun y => mu y * nativePrincipalDefectScalarCoefficient g1 g2 L lam δ R p i j a y) =
      fun y => Q y*f y := by funext y; dsimp only [Q,f,nativePrincipalDefectScalarCoefficient]; ring
  have hrate : r*beta ≤ eps/beta := (le_div_iff₀ hbpos).2 (by nlinarith [hsmall])
  constructor
  · change |(fun y => mu y * nativePrincipalDefectScalarCoefficient g1 g2 L lam δ R p i j a y) x| ≤ _
    rw [he,abs_mul]
    calc
      _ ≤ (Cp*r)*(J*beta) := mul_le_mul hQ0 hf0 (abs_nonneg _) (by positivity)
      _ ≤ D*(r*beta) := by dsimp only [D]; nlinarith [mul_nonneg (mul_nonneg hCp.le hJ.le) (mul_nonneg hr.le hb0)]
      _ ≤ D*(eps/beta) := mul_le_mul_of_nonneg_left hrate hD.le
      _ ≤ (mu x*C)*(eps/beta) := mul_le_mul_of_nonneg_right hDC (div_nonneg heps hb0)
      _ = _ := by ring
  · intro k
    rw [he]
    have hp := directionalFDeriv_smul (coordinateDirection k) Q f hQS hfS x
    simp only [smul_eq_mul] at hp
    rw [hp]
    calc
      _ ≤ |directionalFDeriv (coordinateDirection k) Q x * f x| +
          |Q x * directionalFDeriv (coordinateDirection k) f x| := abs_add_le _ _
      _ = |directionalFDeriv (coordinateDirection k) Q x| * |f x| +
          |Q x| * |directionalFDeriv (coordinateDirection k) f x| := by rw [abs_mul,abs_mul]
      _ ≤ (Cp*r*beta)*(J*beta)+(Cp*r)*(J*beta^2) :=
        add_le_add (mul_le_mul (hQ1 k) hf0 (abs_nonneg _) (by positivity))
          (mul_le_mul hQ0 (hf1 k) (abs_nonneg _) (by positivity))
      _ = D*(r*beta^2) := by dsimp only [D]; ring
      _ ≤ D*eps := mul_le_mul_of_nonneg_left hsmall hD.le
      _ ≤ (mu x*C)*eps := mul_le_mul_of_nonneg_right hDC heps
      _ = _ := by ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
