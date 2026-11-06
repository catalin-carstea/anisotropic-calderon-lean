import Calderon.ActualReferenceDDHigherCLMProducts
import Calderon.ActualNormalizedPrincipalDensityCoefficientJets
import Calderon.ActualReferenceDDHigherProfileJets
import Calderon.ActualMixedDensityRaisingCoefficientJets
import Calderon.ActualPhysicalMixedProfile
import Calderon.ActualPhysicalMixedConnection
import Calderon.ActualPhysicalPureAngular
import Calderon.ActualHorizontalGeometry

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherHCoframeJets ActualReferenceDDHigherCLMProducts
  ActualReferenceDDHigherProfileJets ActualMixedDensityRaisingCoefficientJets ActualMixedDensityHigherCoefficientJets
  ActualMixedDensityScalarZeroForm ActualNormalizedSecondModelErrorAssembly
  ActualPhysicalMixedFirst ActualPhysicalMixedProfile ActualPhysicalMixedConnection ActualPhysicalPureAngular
  ActualHorizontalNormBridge CoordinateBootstrapJets NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
  ReferenceDensityBounds SmoothMetricFrame MovingFrameConnection PrincipalCommutator ConformalDepth
  ReferenceWeightedApproximation MetricOperator
theorem exists_native_mixed_zero_coefficients_uniform_coordinate_word_smallness
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ x ∈ K,
      let beta := actualReferenceBeta g1 L lam δ R p x
      1 ≤ beta →
      coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius δ R p L x →
      referenceRadius δ R p L x * beta^2 ≤ eps →
      ∀ a b c : Fin 3, ∀ w : List (Fin 3), w.length ≤ 2 →
      |coordinateFieldWordPartial w
        (physicalMixedDensityCorrection g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a) x| ≤
          (C * eps) * beta^w.length ∧
      |coordinateFieldWordPartial w
        (physicalMixedProfileCoefficient g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam) a) x| ≤
          (C * eps) * beta^w.length ∧
      |coordinateFieldWordPartial w
        (physicalMixedConnectionCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a b c) x| ≤
          (C * eps) * beta^w.length ∧
      |coordinateFieldWordPartial w
        (physicalPureAngularCoefficient g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam) a b) x| ≤
          (C * eps) * beta^w.length := by
  obtain ⟨M,hM,hgeom⟩ := exists_mixed_principal_density_background_jet_bound g1 hg1 L K hK 3
  obtain ⟨Cr,hCr,hRadius⟩ := exists_referenceRadius_uniform_coordinate_word_bounds g1 hg1 L hL K hK 2
  obtain ⟨J,hJ,hLog⟩ := exists_log_referenceRadius_uniform_positive_coordinate_word_bounds g1 hg1 L hL K hK 3
  obtain ⟨MG,hMG,hGamma⟩ := exists_parameter_coordinate_word_uniform_bound
    (fun t : Fin 3 × Fin 3 × Fin 3 => fun q : ℝ × R3 =>
      referenceFrameConnectionJoint g1 L (fun _ => coordinateDirection t.1) q t.2.1 t.2.2)
    (fun t => contDiff_referenceFrameConnectionJoint g1 hg1 L
      (fun _ => coordinateDirection t.1) contDiff_const t.2.1 t.2.2) K hK 2
  let Cd : ℝ := mixedDensityCorrectionJetConstant 2*M^3
  let Cp : ℝ := 1152*M*J
  let Cc : ℝ := 144*M*MG
  let Cu : ℝ := 576*Cr*M^2
  let C : ℝ := 1+Cd+Cp+Cc+Cu
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hMG0 : 0 ≤ MG := le_trans zero_le_one hMG
  have hCd : 0 ≤ Cd := by dsimp only [Cd,mixedDensityCorrectionJetConstant]; positivity
  have hCp : 0 ≤ Cp := by dsimp only [Cp]; positivity
  have hCc : 0 ≤ Cc := by dsimp only [Cc]; positivity
  have hCu : 0 ≤ Cu := by dsimp only [Cu]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hCdC : Cd ≤ C := by dsimp only [C]; linarith
  have hCpC : Cp ≤ C := by dsimp only [C]; linarith
  have hCcC : Cc ≤ C := by dsimp only [C]; linarith
  have hCuC : Cu ≤ C := by dsimp only [C]; linarith
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall a b c w hw
  let r : ℝ := referenceRadius δ R p L x
  let h := referenceNormalizedPrincipalDifference g1 g2 L lam
  let E (i a : Fin 3) : R3 → ℝ := fun y => referenceCoFrameEntry g1 L i a (lam,y)
  let Flog (j : Fin 3) : R3 → ℝ := directionalFDeriv (coordinateDirection j)
    (fun y => Real.log (referenceRadius δ R p L y))
  let Gam (j b c : Fin 3) : R3 → ℝ := fun y => referenceFrameConnectionCoefficient g1 L lam y
    (coordinateDirection j) b c
  let Ri : R3 → ℝ := fun y => (referenceRadius δ R p L y)⁻¹
  have hr : 0 < r := referenceRadius_pos δ R p L x hδ hR
  have hb0 : 0 ≤ beta := le_trans zero_le_one hb
  have hb2 : 1 ≤ beta^2 := one_le_pow₀ hb
  change r*beta^2 ≤ eps at hsmall
  have hr1 : r ≤ 1 := ((le_mul_of_one_le_right hr.le hb2).trans hsmall).trans heps1
  have hrb1 : r*beta ≤ 1 := by nlinarith
  have herb : eps*r*beta ≤ eps := by nlinarith
  have her : eps*r ≤ eps := by nlinarith
  have hH : ContDiff ℝ ∞ h := contDiff_referenceNormalizedPrincipalDifference g1 g2 hg1 hg2 L lam
  have hHS (i j : Fin 3) : ContDiff ℝ ∞ (fun y => h y i j) :=
    (contDiff_apply_apply ℝ ℝ i j).comp hH
  have hES (i a : Fin 3) : ContDiff ℝ ∞ (E i a) :=
    (contDiff_referenceCoFrameEntry g1 hg1 L i a).comp (contDiff_const.prodMk contDiff_id)
  have hLS (j : Fin 3) : ContDiff ℝ ∞ (Flog j) :=
    contDiff_directionalFDeriv (coordinateDirection j) _ (contDiff_log_referenceRadius_profile δ R L p hδ hR)
  have hJointEq (j b c : Fin 3) :
      (fun y => referenceFrameConnectionJoint g1 L (fun _ => coordinateDirection j) (lam,y) b c) = Gam j b c := by
    funext y
    exact referenceFrameConnectionJoint_eq g1 hg1 L (fun _ => coordinateDirection j) (lam,y) b c
  have hGS (j b c : Fin 3) : ContDiff ℝ ∞ (Gam j b c) := by
    rw [← hJointEq j b c]
    exact (contDiff_referenceFrameConnectionJoint g1 hg1 L
      (fun _ => coordinateDirection j) contDiff_const b c).comp (contDiff_const.prodMk contDiff_id)
  have hRiS : ContDiff ℝ ∞ Ri :=
    (ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δ R p L hδ hR).inv
      (fun y => (referenceRadius_pos δ R p L y hδ hR).ne')
  have hHj (i j : Fin 3) : HasCoordinateWordJetBound 2 (fun y => h y i j) x (eps*r) beta 0 :=
    hasCoordinateWordJetBound_component_of_H8 2 (by norm_num) h hHS x i j eps beta δ R L p
      heps hb hδ hR hH8
  have hEj (i a : Fin 3) : HasCoordinateWordJetBound 2 (E i a) x M beta 0 := by
    intro v hv
    have ht := (hgeom lam hlam x hx).1.2.1 v (by omega) i a
    calc
      ‖coordinateFieldWordPartial v (E i a) x‖ = |coordinateFieldWordPartial v (E i a) x| := Real.norm_eq_abs _
      _ ≤ M := ht
      _ ≤ M*beta^(0+v.length) := by
        simpa only [Nat.zero_add,mul_one] using
          mul_le_mul_of_nonneg_left (one_le_pow₀ hb) hM0
  have hLj (j : Fin 3) : HasCoordinateWordJetBound 2 (Flog j) x J beta 1 := by
    intro v hv
    have ht := hLog lam hlam δ hδ hδ1 R hR p hp x hx (v++[j])
      (by simp only [List.length_append,List.length_singleton]; omega)
      (by simp only [List.length_append,List.length_singleton]; omega)
    simpa only [Flog,coordinateFieldWordPartial_append,coordinateFieldWordPartial,
      List.length_append,List.length_singleton,Nat.add_comm,beta,actualReferenceBeta,Real.norm_eq_abs] using ht
  have hGj (j b c : Fin 3) : HasCoordinateWordJetBound 2 (Gam j b c) x MG beta 0 := by
    intro v hv
    have ht := hGamma lam hlam x hx (j,b,c) v hv
    rw [hJointEq j b c] at ht
    exact ht.trans (by simpa only [Nat.zero_add,mul_one] using
      mul_le_mul_of_nonneg_left (one_le_pow₀ hb) hMG0)
  have hRij : HasCoordinateWordJetBound 2 Ri x (Cr*r⁻¹) beta 0 := by
    intro v hv
    have ht := (hRadius lam hlam δ hδ hδ1 R hR p hp x hx v hv).2
    simpa only [Ri,r,beta,actualReferenceBeta,Real.norm_eq_abs,Nat.zero_add] using ht
  have hHE (i j a : Fin 3) : HasCoordinateWordJetBound 2 (fun y => h y i j*E i a y) x
      (4*eps*r*M) beta 0 := by
    have ht := hasCoordinateWordJetBound_mul 2 (fun y => h y i j) (E i a)
      (hHS i j) (hES i a) x (eps*r) M beta 0 0 (mul_nonneg heps hr.le) hM0 hb0 (hHj i j) (hEj i a)
    convert ht using 1 <;> simp only [show (2 : ℝ)^2=4 by norm_num,Nat.add_zero] <;> ring
  have hProfTerm (i j : Fin 3) : HasCoordinateWordJetBound 2
      (fun y => (h y i j*E i a y)*Flog j y) x (16*M*J*eps*r) beta 1 := by
    have ht := hasCoordinateWordJetBound_mul 2 (fun y => h y i j*E i a y) (Flog j)
      ((hHS i j).mul (hES i a)) (hLS j) x (4*eps*r*M) J beta 0 1
      (by positivity) hJ.le hb0 (hHE i j a) (hLj j)
    convert ht using 1 <;> simp only [show (2 : ℝ)^2=4 by norm_num,Nat.zero_add] <;> ring
  have hProfSum := hasCoordinateWordJetBound_sum 2
    (fun i y => ∑ j : Fin 3, (h y i j*E i a y)*Flog j y)
    (fun i => ContDiff.sum fun j _ => ((hHS i j).mul (hES i a)).mul (hLS j)) x
    (3*(16*M*J*eps*r)) beta 1
    (fun i => by
      have ht := hasCoordinateWordJetBound_sum 2 (fun j y => (h y i j*E i a y)*Flog j y)
        (fun j => ((hHS i j).mul (hES i a)).mul (hLS j)) x (16*M*J*eps*r) beta 1 (hProfTerm i)
      simpa only [Fintype.card_fin,Nat.cast_ofNat] using ht)
  have hProfSum' : HasCoordinateWordJetBound 2
      (fun y => ∑ i : Fin 3, ∑ j : Fin 3, (h y i j*E i a y)*Flog j y) x
      (144*M*J*eps*r) beta 1 := by
    convert hProfSum using 1 <;> simp only [Fintype.card_fin,Nat.cast_ofNat] <;> ring
  have hTwo : HasCoordinateWordJetBound 2 (fun _ : R3 => (2 : ℝ)) x 2 beta 0 :=
    hasCoordinateWordJetBound_const_normed 2 (2 : ℝ) x 2 beta (by norm_num) hb0
  have hProfj : HasCoordinateWordJetBound 2 (physicalMixedProfileCoefficient g1 L lam δ R p h a) x
      (Cp*eps*r) beta 1 := by
    have ht := hasCoordinateWordJetBound_mul 2 (fun _ : R3 => (2 : ℝ))
      (fun y => ∑ i : Fin 3, ∑ j : Fin 3, (h y i j*E i a y)*Flog j y)
      contDiff_const (ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
        ((hHS i j).mul (hES i a)).mul (hLS j)) x 2 (144*M*J*eps*r) beta 0 1
      (by norm_num) (by positivity) hb0 hTwo hProfSum'
    unfold physicalMixedProfileCoefficient
    convert ht using 1 <;> simp only [show (2 : ℝ)^2=4 by norm_num,Nat.zero_add,Cp] <;> ring
  have hConnTerm (i j : Fin 3) : HasCoordinateWordJetBound 2
      (fun y => (h y i j*E i a y)*Gam j b c y) x (16*M*MG*eps*r) beta 0 := by
    have ht := hasCoordinateWordJetBound_mul 2 (fun y => h y i j*E i a y) (Gam j b c)
      ((hHS i j).mul (hES i a)) (hGS j b c) x (4*eps*r*M) MG beta 0 0
      (by positivity) hMG0 hb0 (hHE i j a) (hGj j b c)
    convert ht using 1 <;> simp only [show (2 : ℝ)^2=4 by norm_num,Nat.add_zero] <;> ring
  have hConnSum := hasCoordinateWordJetBound_sum 2
    (fun i y => ∑ j : Fin 3, (h y i j*E i a y)*Gam j b c y)
    (fun i => ContDiff.sum fun j _ => ((hHS i j).mul (hES i a)).mul (hGS j b c)) x
    (3*(16*M*MG*eps*r)) beta 0
    (fun i => by
      have ht := hasCoordinateWordJetBound_sum 2 (fun j y => (h y i j*E i a y)*Gam j b c y)
        (fun j => ((hHS i j).mul (hES i a)).mul (hGS j b c)) x (16*M*MG*eps*r) beta 0 (hConnTerm i)
      simpa only [Fintype.card_fin,Nat.cast_ofNat] using ht)
  have hConnj : HasCoordinateWordJetBound 2 (physicalMixedConnectionCoefficient g1 L lam h a b c) x
      (Cc*eps*r) beta 0 := by
    unfold physicalMixedConnectionCoefficient
    convert hConnSum using 1 <;> simp only [Fintype.card_fin,Nat.cast_ofNat,Cc] <;> ring
  have hHR (i j : Fin 3) : HasCoordinateWordJetBound 2 (fun y => h y i j*Ri y) x
      (4*Cr*eps) beta 0 := by
    have ht := hasCoordinateWordJetBound_mul 2 (fun y => h y i j) Ri (hHS i j) hRiS x
      (eps*r) (Cr*r⁻¹) beta 0 0 (mul_nonneg heps hr.le) (by positivity) hb0 (hHj i j) hRij
    have heq : (2 : ℝ)^2*(eps*r)*(Cr*r⁻¹)=4*Cr*eps := by
      rw [show (2 : ℝ)^2=4 by norm_num]
      field_simp [hr.ne']
      <;> ring
    simpa only [heq,Nat.add_zero] using ht
  have hPureTerm (i j : Fin 3) : HasCoordinateWordJetBound 2
      (fun y => ((h y i j*Ri y)*E i a y)*E j b y) x (64*Cr*M^2*eps) beta 0 := by
    have h1 := hasCoordinateWordJetBound_mul 2 (fun y => h y i j*Ri y) (E i a)
      ((hHS i j).mul hRiS) (hES i a) x (4*Cr*eps) M beta 0 0
      (by positivity) hM0 hb0 (hHR i j) (hEj i a)
    have ht := hasCoordinateWordJetBound_mul 2 (fun y => (h y i j*Ri y)*E i a y) (E j b)
      (((hHS i j).mul hRiS).mul (hES i a)) (hES j b) x
      ((2 : ℝ)^2*(4*Cr*eps)*M) M beta (0+0) 0
      (by positivity) hM0 hb0 h1 (hEj j b)
    convert ht using 1 <;> simp only [show (2 : ℝ)^2=4 by norm_num,Nat.add_zero] <;> ring
  have hPureSum := hasCoordinateWordJetBound_sum 2
    (fun i y => ∑ j : Fin 3, ((h y i j*Ri y)*E i a y)*E j b y)
    (fun i => ContDiff.sum fun j _ => (((hHS i j).mul hRiS).mul (hES i a)).mul (hES j b)) x
    (3*(64*Cr*M^2*eps)) beta 0
    (fun i => by
      have ht := hasCoordinateWordJetBound_sum 2 (fun j y => ((h y i j*Ri y)*E i a y)*E j b y)
        (fun j => (((hHS i j).mul hRiS).mul (hES i a)).mul (hES j b)) x (64*Cr*M^2*eps) beta 0 (hPureTerm i)
      simpa only [Fintype.card_fin,Nat.cast_ofNat] using ht)
  have hPurej : HasCoordinateWordJetBound 2 (physicalPureAngularCoefficient g1 L lam δ R p h a b) x
      (Cu*eps) beta 0 := by
    unfold physicalPureAngularCoefficient
    convert hPureSum using 1 <;> simp only [div_eq_mul_inv,Fintype.card_fin,Nat.cast_ofNat,Cu] <;> ring
  have hDens := abs_physicalMixedDensityCorrection_coordinate_word_le g1 g2 hg1 hg2 L lam x
    eps r M 2 (by norm_num) heps hr.le hM0 (hgeom lam hlam x hx).1 hH8 w hw a
  refine ⟨?_,?_,?_,?_⟩
  · calc
      _ ≤ Cd*eps*r := hDens
      _ ≤ Cd*eps := by nlinarith
      _ ≤ (C*eps)*beta^w.length := by
        have hp0 : 1 ≤ beta^w.length := one_le_pow₀ hb
        exact (mul_le_mul_of_nonneg_right hCdC heps).trans
          (le_mul_of_one_le_right (mul_nonneg hC.le heps) hp0)
  · have ht := hProfj w hw
    rw [Real.norm_eq_abs] at ht
    have hbpow : beta^(1+w.length)=beta*beta^w.length := by rw [pow_add]; simp
    calc
      _ ≤ (Cp*eps*r)*beta^(1+w.length) := ht
      _ = (Cp*(eps*r*beta))*beta^w.length := by rw [hbpow]; ring
      _ ≤ (Cp*eps)*beta^w.length := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left herb hCp) (pow_nonneg hb0 _)
      _ ≤ (C*eps)*beta^w.length := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCpC heps) (pow_nonneg hb0 _)
  · have ht := hConnj w hw
    rw [Real.norm_eq_abs] at ht
    calc
      _ ≤ (Cc*eps*r)*beta^(0+w.length) := ht
      _ ≤ (C*eps)*beta^w.length := by
        simpa only [Nat.zero_add,mul_assoc] using mul_le_mul_of_nonneg_right
          ((mul_le_mul_of_nonneg_left her hCc).trans (mul_le_mul_of_nonneg_right hCcC heps))
          (pow_nonneg hb0 _)
  · have ht := hPurej w hw
    rw [Real.norm_eq_abs] at ht
    exact ht.trans (by simpa only [Nat.zero_add] using
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCuC heps) (pow_nonneg hb0 _))

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
