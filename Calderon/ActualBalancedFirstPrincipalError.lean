import Calderon.NaturalAdjointNormalForm
import Calderon.ActualPerturbedDefect
import Calderon.BalancedFrameAngularShift
import Calderon.FixedProfileBounds
import Calderon.SectionFiveNormalizedSecondForm

noncomputable section
open MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.ActualBalancedFirstPrincipalError
open SphereHarmonic SpectralCoreRegularity SpectralWeightedGraph AngularShiftGraph
  BalancedAngularShift BalancedFrameAngularShift SmoothMetricFrame
  ReferenceDensityBounds PrincipalCommutator ActualScalarPrincipalAdjoint
  ActualPerturbedDefect PerturbedDensityAdjoint ConformalDepth RadiusProfile
  AmbientAngularShift SmoothSphereFields SmoothAngularApplication SectionFiveErrorForms

def frameEntry (g : MatrixField) (L : ℝ) (i k : Fin 3) (z : ℝ × R3) : ℝ :=
  referenceMetricGramFrame g L z i k

def frameContraction (S : Fin 3 → SphereL2 →L[ℝ] SphereL2)
    (g : MatrixField) (L lam : ℝ) (k : Fin 3) (x : R3) : SphereL2 →L[ℝ] SphereL2 :=
  ∑ i, frameEntry g L i k (lam,x) • S i

def actualBeta (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (x : R3) : ℝ :=
  metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
    (fun y => Real.log (referenceRadius δ R p L y)) x

def normalizedPrincipalDerivative (g : MatrixField) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (k i j : Fin 3) (x : R3) : ℝ :=
  actualBeta g L lam δ R p x * directionalFDeriv (coordinateDirection k)
    (fun y => actualPrincipalMatrix g L lam δ R p h y i j) x

def normalizedFirstPrincipalLowering (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (k i j : Fin 3) (x : R3) : SphereL2 →L[ℝ] SphereL2 :=
  normalizedPrincipalDerivative g L lam δ R p h k i j x •
    (-frameContraction (balancedDerivative hF hO hD) g L lam k x)

def normalizedFirstPrincipalRaising (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (k i j : Fin 3) (x : R3) : SphereL2 →L[ℝ] SphereL2 :=
  normalizedPrincipalDerivative g L lam δ R p h k i j x •
    (-frameContraction (balancedRaising hF hO hD) g L lam k x)

lemma contDiff_frameEntry (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (i k : Fin 3) : ContDiff ℝ ∞ (frameEntry g L i k) := by
  exact ((contDiff_piLp_apply (p := (2 : ℝ≥0∞)) (i := k) :
    ContDiff ℝ ∞ (fun v : R3 => v k)).comp
      (contDiff_referenceMetricGramFrame g hg L i))

theorem exists_frameEntry_uniform_two_jet_bound (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K,
      ∀ i k, ∀ s : JetTag, |coordinateJetFamily (frameEntry g L i k) s (lam,x)| ≤ M := by
  obtain ⟨M,hM,hbound⟩ := exists_uniform_bound_finite_family
    (fun t : (Fin 3 × Fin 3) × JetTag => coordinateJetFamily (frameEntry g L t.1.1 t.1.2) t.2)
    (fun t => continuous_coordinateJetFamily _ (contDiff_frameEntry g hg L t.1.1 t.1.2) t.2) K hK
  exact ⟨M,hM,fun lam hlam x hx i k s => hbound lam hlam x hx ((i,k),s)⟩

lemma contDiff_frameContraction (S : Fin 3 → SphereL2 →L[ℝ] SphereL2)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : Fin 3) :
    ContDiff ℝ ∞ (frameContraction S g L lam k) := by
  unfold frameContraction
  apply ContDiff.sum
  intro i _
  exact ((contDiff_frameEntry g hg L i k).comp
    (contDiff_const.prodMk contDiff_id : ContDiff ℝ ∞ (fun y : R3 => (lam,y)))).smul contDiff_const

lemma directional_frameContraction (S : Fin 3 → SphereL2 →L[ℝ] SphereL2)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (k l : Fin 3) (x : R3) :
    directionalFDeriv (coordinateDirection l) (frameContraction S g L lam k) x =
      ∑ i, familyDirectionalDeriv l (frameEntry g L i k) (lam,x) • S i := by
  have hs (i : Fin 3) : ContDiff ℝ ∞ (fun y : R3 => frameEntry g L i k (lam,y)) :=
    (contDiff_frameEntry g hg L i k).comp (contDiff_const.prodMk contDiff_id)
  have ht (i : Fin 3) : ContDiff ℝ ∞ (fun y : R3 => frameEntry g L i k (lam,y) • S i) :=
    (hs i).smul contDiff_const
  unfold frameContraction directionalFDeriv
  rw [fderiv_fun_sum (fun i _ => (ht i).differentiable (by simp) x)]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  have he := directionalFDeriv_smul (coordinateDirection l)
    (fun y => frameEntry g L i k (lam,y)) (fun _ => S i) (hs i) contDiff_const x
  simp only [directionalFDeriv,fderiv_const_apply,ContinuousLinearMap.zero_apply,
    smul_zero,add_zero] at he
  rw [he]
  rfl

lemma norm_finite_contraction_le (S : Fin 3 → SphereL2 →L[ℝ] SphereL2)
    (c : Fin 3 → ℝ) (B M : ℝ) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hS : ∀ i, ‖S i‖ ≤ B) (hc : ∀ i, |c i| ≤ M) :
    ‖∑ i, c i • S i‖ ≤ 3 * B * M := by
  calc
    _ ≤ ∑ i, ‖c i • S i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, M * B := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul (hc i) (hS i) (norm_nonneg _) hM
    _ = _ := by simp; ring

lemma contDiff_actualBeta (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hL : 0 < L) (hδ : 0 < δ) (hR : 0 < R) :
    ContDiff ℝ ∞ (actualBeta g L lam δ R p) := by
  let t : R3 → ℝ := referenceDepth L
  have ht : ContDiff ℝ ∞ t := contDiff_referenceDepth L
  have hE : ContDiff ℝ ∞ (fun y : R3 => Real.exp (t y / δ)) := (ht.div_const δ).exp
  have hP : ContDiff ℝ ∞ (fun y : R3 => 1 + Real.exp (t y / δ)) := contDiff_const.add hE
  have hPpos (y : R3) : 0 < 1 + Real.exp (t y / δ) :=
    add_pos zero_lt_one (Real.exp_pos _)
  have hlogP : ContDiff ℝ ∞ (fun y : R3 => Real.log (1 + Real.exp (t y / δ))) :=
    hP.log (fun y => (hPpos y).ne')
  have hden : ContDiff ℝ ∞ (fun y : R3 =>
      δ * (1 + Real.exp (t y / δ)) * Real.log (1 + Real.exp (t y / δ))) :=
    (contDiff_const.mul hP).mul hlogP
  have hdenpos (y : R3) :
      0 < δ * (1 + Real.exp (t y / δ)) * Real.log (1 + Real.exp (t y / δ)) :=
    mul_pos (mul_pos hδ (hPpos y)) (log_exp_add_one_pos (t y / δ))
  have hquot : ContDiff ℝ ∞ (fun y : R3 =>
      Real.exp (t y / δ) /
        (δ * (1 + Real.exp (t y / δ)) * Real.log (1 + Real.exp (t y / δ)))) :=
    hE.div hden (fun y => (hdenpos y).ne')
  have hSlope : ContDiff ℝ ∞ (fun y : R3 => logSlope δ (t y)) := by
    simpa only [logSlope] using hquot
  have hinc : ContDiff ℝ ∞ (fun y : R3 => (lam,y)) :=
    contDiff_const.prodMk contDiff_id
  have hbaseJoint := (contDiff_dilatedReferenceDepth_metricNorm g hg L hL).comp hinc
  have hbase : ContDiff ℝ ∞ (fun y : R3 =>
      metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L) (referenceDepth L) y) := by
    simpa only [Function.comp_def] using hbaseJoint
  have hproduct : ContDiff ℝ ∞ (fun y : R3 =>
      ((p : ℝ) * logSlope δ (t y)) *
        metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L) (referenceDepth L) y) :=
    (contDiff_const.mul hSlope).mul hbase
  have he : actualBeta g L lam δ R p = fun y : R3 =>
      ((p : ℝ) * logSlope δ (t y)) *
        metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L) (referenceDepth L) y := by
    funext y
    change metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
      (fun z => Real.log (referenceRadius δ R p L z)) y = _
    rw [log_referenceRadius δ R p L hδ hR]
    exact metricDifferentialNorm_logProfile _ δ (Real.log R) p (referenceDepth L) y hδ
      ((contDiff_referenceDepth L).differentiable (by simp) y)
  rw [he]
  exact hproduct

lemma contDiff_normalizedPrincipalDerivative (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (h : MatrixField) (k i j : Fin 3)
    (hL : 0 < L) (hδ : 0 < δ) (hR : 0 < R)
    (hh : ∀ a b, ContDiff ℝ ∞ (fun x => h x a b)) :
    ContDiff ℝ ∞ (normalizedPrincipalDerivative g L lam δ R p h k i j) := by
  exact (contDiff_actualBeta g hg L lam δ R p hL hδ hR).mul
    (contDiff_directionalFDeriv (coordinateDirection k) _
      (contDiff_actualPrincipalMatrix_entry g hg L lam δ R p h hδ hR hh i j))

lemma contDiff_normalizedFirstPrincipalLowering (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (k i j : Fin 3) (hL : 0 < L) (hδ : 0 < δ) (hR : 0 < R)
    (hh : ∀ a b, ContDiff ℝ ∞ (fun x => h x a b)) :
    ContDiff ℝ ∞ (normalizedFirstPrincipalLowering hF hO hD g L lam δ R p h k i j) := by
  exact (contDiff_normalizedPrincipalDerivative g hg L lam δ R p h k i j hL hδ hR hh).smul
    (contDiff_frameContraction (balancedDerivative hF hO hD) g hg L lam k).neg

lemma contDiff_normalizedFirstPrincipalRaising (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (k i j : Fin 3) (hL : 0 < L) (hδ : 0 < δ) (hR : 0 < R)
    (hh : ∀ a b, ContDiff ℝ ∞ (fun x => h x a b)) :
    ContDiff ℝ ∞ (normalizedFirstPrincipalRaising hF hO hD g L lam δ R p h k i j) := by
  exact (contDiff_normalizedPrincipalDerivative g hg L lam δ R p h k i j hL hδ hR hh).smul
    (contDiff_frameContraction (balancedRaising hF hO hD) g hg L lam k).neg

theorem exists_actual_principal_first_second_bounds (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ h : MatrixField,
      (∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) →
      (∀ i j k l, TwoJetBound (coordinateDirection k) (coordinateDirection l)
        (fun y => h y i j) x (eps * referenceRadius δ R p L x)) →
      1 ≤ actualBeta g L lam δ R p x →
      referenceRadius δ R p L x * (actualBeta g L lam δ R p x)^2 ≤ eps →
      ∀ i j k l,
        |directionalFDeriv (coordinateDirection k)
          (fun y => actualPrincipalMatrix g L lam δ R p h y i j) x| ≤
            C1 * eps / actualBeta g L lam δ R p x ∧
        |directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k)
          (fun y => actualPrincipalMatrix g L lam δ R p h y i j)) x| ≤ C2 * eps := by
  obtain ⟨M,hM,hbackground⟩ := exists_referenceBackground_uniform_two_jet_bound g hg L K hK
  obtain ⟨J1,hJ1,hjet1⟩ := exists_dilated_referenceRadius_fixed_uniform_radius_jet_bounds
    g hg L hL K hK 1
  obtain ⟨J2,hJ2,hjet2⟩ := exists_dilated_referenceRadius_fixed_uniform_radius_jet_bounds
    g hg L hL K hK 2
  refine ⟨(J1+2)*M*(M+1),(J2+4*J1+4)*M*(M+1),by positivity,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh hhjet hb hsmall i j k l
  let q : R3 → ℝ := fun y => referenceInverseEntryFamily g L i j (lam,y)
  have hq : ContDiff ℝ ∞ q := (contDiff_referenceInverseEntryFamily g hg L i j).comp
    (contDiff_const.prodMk contDiff_id)
  have hmu : TwoJetBound (coordinateDirection k) (coordinateDirection l) (fun _ : R3 => (1 : ℝ)) x M := by
    have hzero (X : R3) : directionalFDeriv X (fun _ : R3 => (1 : ℝ)) = fun _ => (0 : ℝ) := by
      funext y
      simp only [directionalFDeriv,fderiv_const_apply,ContinuousLinearMap.zero_apply]
    refine ⟨by simpa using hM,?_,?_,?_⟩
    · rw [hzero]
      simpa only [abs_zero] using (show 0 ≤ M by linarith)
    · rw [hzero]
      simpa only [abs_zero] using (show 0 ≤ M by linarith)
    · rw [hzero]
      simp only [directionalFDeriv,fderiv_const_apply,ContinuousLinearMap.zero_apply,abs_zero]
      linarith
  have hqjet : TwoJetBound (coordinateDirection k) (coordinateDirection l) q x M := by
    refine ⟨?_,?_,?_,?_⟩
    · exact hbackground lam hlam x hx (.inr (i,j)) (.inl ())
    · exact hbackground lam hlam x hx (.inr (i,j)) (.inr (.inl k))
    · exact hbackground lam hlam x hx (.inr (i,j)) (.inr (.inl l))
    · exact hbackground lam hlam x hx (.inr (i,j)) (.inr (.inr (k,l)))
  have hr := contDiff_referenceRadius_actual δ R p L hδ hR
  have h1 := (hjet1 lam hlam δ hδ hδ1 R hR p hp x hx).1
  have h2 := (hjet2 lam hlam δ hδ hδ1 R hR p hp x hx).1
  have h1k := (abs_coordinate_first_le k (referenceRadius δ R p L) x).trans h1
  have h1l := (abs_coordinate_first_le l (referenceRadius δ R p L) x).trans h1
  have h2kl := (abs_coordinate_second_le k l (referenceRadius δ R p L) hr x).trans h2
  have hresult := density_principal_first_second_bounds (coordinateDirection k) (coordinateDirection l)
    (fun _ => (1 : ℝ)) (referenceRadius δ R p L) q (fun y => h y i j)
    contDiff_const hr hq (hh i j) x M J1 J2 (actualBeta g L lam δ R p x) eps
    hM hJ1.le hJ2.le hb heps heps1 (referenceRadius_pos δ R p L x hδ hR) hsmall
    hmu hqjet (hhjet i j k l)
    (by simpa only [pow_one,actualBeta] using h1k)
    (by simpa only [pow_one,actualBeta] using h1l)
    (by simpa only [actualBeta] using h2kl)
  have he : PerturbedDensityAdjoint.densityPrincipalEntry (fun _ : R3 => (1 : ℝ))
      (referenceRadius δ R p L) q (fun y => h y i j) =
      (fun y => actualPrincipalMatrix g L lam δ R p h y i j) := by
    funext y
    unfold PerturbedDensityAdjoint.densityPrincipalEntry PerturbedDensityAdjoint.principalEntry
    simp only [one_mul,q,actualPrincipalMatrix]
  rw [he] at hresult
  exact hresult

lemma normalized_scalar_jet_bound (beta a : R3 → ℝ) (k l : Fin 3)
    (hb : ContDiff ℝ ∞ beta) (ha : ContDiff ℝ ∞ a) (x : R3)
    (C1 C2 D eps : ℝ) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hD : 0 ≤ D)
    (heps : 0 ≤ eps) (hbeta : 1 ≤ beta x)
    (hd : |directionalFDeriv (coordinateDirection k) a x| ≤ C1 * eps / beta x)
    (hdd : |directionalFDeriv (coordinateDirection l)
      (directionalFDeriv (coordinateDirection k) a) x| ≤ C2 * eps)
    (hdb : |directionalFDeriv (coordinateDirection l) beta x| ≤ D * (beta x)^2) :
    |beta x * directionalFDeriv (coordinateDirection k) a x| ≤ C1 * eps ∧
    |directionalFDeriv (coordinateDirection l)
      (fun y => beta y * directionalFDeriv (coordinateDirection k) a y) x| ≤
        (D * C1 + C2) * eps * beta x := by
  have hpos : 0 < beta x := lt_of_lt_of_le zero_lt_one hbeta
  have hs : beta x * |directionalFDeriv (coordinateDirection k) a x| ≤ C1 * eps := by
    calc
      _ ≤ beta x * (C1 * eps / beta x) := mul_le_mul_of_nonneg_left hd hpos.le
      _ = _ := by field_simp
  have hterm1 : |directionalFDeriv (coordinateDirection l) beta x| *
      |directionalFDeriv (coordinateDirection k) a x| ≤ D * C1 * eps * beta x := by
    calc
      _ ≤ (D * (beta x)^2) * |directionalFDeriv (coordinateDirection k) a x| :=
        mul_le_mul_of_nonneg_right hdb (abs_nonneg _)
      _ = (D * beta x) * (beta x * |directionalFDeriv (coordinateDirection k) a x|) := by ring
      _ ≤ (D * beta x) * (C1 * eps) := mul_le_mul_of_nonneg_left hs (mul_nonneg hD hpos.le)
      _ = _ := by ring
  have hterm2 : beta x * |directionalFDeriv (coordinateDirection l)
      (directionalFDeriv (coordinateDirection k) a) x| ≤ C2 * eps * beta x := by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hdd hpos.le
  refine ⟨by simpa only [abs_mul,abs_of_pos hpos] using hs,?_⟩
  rw [directional_mul _ beta _ hb (contDiff_directionalFDeriv (coordinateDirection k) a ha) x]
  calc
    _ ≤ |directionalFDeriv (coordinateDirection l) beta x *
        directionalFDeriv (coordinateDirection k) a x| +
        |beta x * directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k) a) x| := abs_add_le _ _
    _ ≤ D * C1 * eps * beta x + C2 * eps * beta x := by
      simpa only [abs_mul,abs_of_pos hpos] using add_le_add hterm1 hterm2
    _ = _ := by ring

lemma norm_scalar_frame_contraction_bounds
    (S : Fin 3 → SphereL2 →L[ℝ] SphereL2) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (k l : Fin 3) (c : R3 → ℝ) (hc : ContDiff ℝ ∞ c) (x : R3)
    (B M A E beta eps : ℝ) (hB : 0 ≤ B) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hE : 0 ≤ E) (heps : 0 ≤ eps) (hbeta : 1 ≤ beta)
    (hS : ∀ i, ‖S i‖ ≤ B)
    (hf : ∀ i, |frameEntry g L i k (lam,x)| ≤ M)
    (hdf : ∀ i, |familyDirectionalDeriv l (frameEntry g L i k) (lam,x)| ≤ M)
    (hc0 : |c x| ≤ A * eps)
    (hc1 : |directionalFDeriv (coordinateDirection l) c x| ≤ E * eps * beta) :
    ‖c x • (-frameContraction S g L lam k x)‖ ≤ 3 * B * M * A * eps ∧
    ‖directionalFDeriv (coordinateDirection l)
      (fun y => c y • (-frameContraction S g L lam k y)) x‖ ≤
        3 * B * M * (E + A) * eps * beta := by
  have hF : ‖frameContraction S g L lam k x‖ ≤ 3 * B * M :=
    norm_finite_contraction_le S _ B M hB hM hS hf
  have hDF : ‖directionalFDeriv (coordinateDirection l) (frameContraction S g L lam k) x‖ ≤ 3 * B * M := by
    rw [directional_frameContraction S g hg L lam k l x]
    exact norm_finite_contraction_le S _ B M hB hM hS hdf
  have hneg : ContDiff ℝ ∞ (fun y => -frameContraction S g L lam k y) :=
    (contDiff_frameContraction S g hg L lam k).neg
  have hnDF : ‖directionalFDeriv (coordinateDirection l) (fun y => -frameContraction S g L lam k y) x‖ ≤ 3 * B * M := by
    simpa only [directionalFDeriv,fderiv_fun_neg,ContinuousLinearMap.neg_apply,norm_neg] using hDF
  constructor
  · rw [norm_smul,Real.norm_eq_abs,norm_neg]
    calc
      _ ≤ (A * eps) * (3 * B * M) := mul_le_mul hc0 hF (norm_nonneg _) (mul_nonneg hA heps)
      _ = _ := by ring
  · rw [directionalFDeriv_smul _ c _ hc hneg x]
    calc
      _ ≤ ‖directionalFDeriv (coordinateDirection l) c x • (-frameContraction S g L lam k x)‖ +
          ‖c x • directionalFDeriv (coordinateDirection l) (fun y => -frameContraction S g L lam k y) x‖ := norm_add_le _ _
      _ = |directionalFDeriv (coordinateDirection l) c x| * ‖frameContraction S g L lam k x‖ +
          |c x| * ‖directionalFDeriv (coordinateDirection l) (fun y => -frameContraction S g L lam k y) x‖ := by
        simp only [norm_smul,Real.norm_eq_abs,norm_neg]
      _ ≤ (E * eps * beta) * (3 * B * M) + (A * eps) * (3 * B * M) := by
        exact add_le_add (mul_le_mul hc1 hF (norm_nonneg _) (by positivity))
          (mul_le_mul hc0 hnDF (norm_nonneg _) (mul_nonneg hA heps))
      _ ≤ 3 * B * M * (E + A) * eps * beta := by
        have ha := mul_le_mul_of_nonneg_left hbeta (show 0 ≤ 3 * B * M * A * eps by positivity)
        nlinarith

theorem exists_normalizedFirstPrincipal_uniform_bounds (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ Cw Cdw : ℝ, 0 < Cw ∧ 0 < Cdw ∧
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ h : MatrixField,
      (∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) →
      (∀ i j k l, TwoJetBound (coordinateDirection k) (coordinateDirection l)
        (fun y => h y i j) x (eps * referenceRadius δ R p L x)) →
      1 ≤ actualBeta g L lam δ R p x →
      referenceRadius δ R p L x * (actualBeta g L lam δ R p x)^2 ≤ eps →
      ∀ k i j l,
        ‖normalizedFirstPrincipalLowering hF hO hD g L lam δ R p h k i j x‖ ≤ Cw * eps ∧
        ‖normalizedFirstPrincipalRaising hF hO hD g L lam δ R p h k i j x‖ ≤ Cw * eps ∧
        ‖fderiv ℝ (normalizedFirstPrincipalLowering hF hO hD g L lam δ R p h k i j)
          x (coordinateDirection l)‖ ≤ Cdw * eps * actualBeta g L lam δ R p x ∧
        ‖fderiv ℝ (normalizedFirstPrincipalRaising hF hO hD g L lam δ R p h k i j)
          x (coordinateDirection l)‖ ≤ Cdw * eps * actualBeta g L lam δ R p x := by
  obtain ⟨M,hM,hframe⟩ := exists_frameEntry_uniform_two_jet_bound g hg L K hK
  obtain ⟨C1,C2,hC1,hC2,hprincipal⟩ := exists_actual_principal_first_second_bounds g hg L hL K hK
  obtain ⟨D,hDpos,hbetaDer⟩ := exists_dilated_referenceRadius_uniform_beta_derivative_bounds_at g hg K hK L hL
  refine ⟨12*M*C1,12*M*((D+1)*C1+C2),by positivity,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh hhjet hb hsmall k i j l
  have ha := contDiff_actualPrincipalMatrix_entry g hg L lam δ R p h hδ hR hh i j
  have hbeta := contDiff_actualBeta g hg L lam δ R p hL hδ hR
  have hentry := hprincipal lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh hhjet hb hsmall i j k l
  have hnormDb := (hbetaDer lam hlam δ hδ hδ1 R hR p hp x hx).1
  have hdb : |directionalFDeriv (coordinateDirection l) (actualBeta g L lam δ R p) x| ≤
      D * (actualBeta g L lam δ R p x)^2 := by
    have ht := (fderiv ℝ (actualBeta g L lam δ R p) x).le_opNorm (coordinateDirection l)
    have hn : ‖fderiv ℝ (actualBeta g L lam δ R p) x‖ ≤ D * (actualBeta g L lam δ R p x)^2 := hnormDb
    simpa only [directionalFDeriv,Real.norm_eq_abs,norm_coordinateDirection,mul_one] using
      ht.trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  have hcjet := normalized_scalar_jet_bound (actualBeta g L lam δ R p)
    (fun y => actualPrincipalMatrix g L lam δ R p h y i j) k l hbeta ha x
    C1 C2 D eps hC1.le hC2.le hDpos.le heps hb hentry.1 hentry.2 hdb
  have hc := contDiff_normalizedPrincipalDerivative g hg L lam δ R p h k i j hL hδ hR hh
  have hf (b : Fin 3) : |frameEntry g L b k (lam,x)| ≤ M := hframe lam hlam x hx b k (.inl ())
  have hdf (b : Fin 3) : |familyDirectionalDeriv l (frameEntry g L b k) (lam,x)| ≤ M :=
    hframe lam hlam x hx b k (.inr (.inl l))
  have hLower := norm_scalar_frame_contraction_bounds (balancedDerivative hF hO hD) g hg L lam k l
    (normalizedPrincipalDerivative g L lam δ R p h k i j) hc x 4 M C1 (D*C1+C2)
    (actualBeta g L lam δ R p x) eps (by norm_num) (by linarith) hC1.le (by positivity) heps hb
    (norm_balancedDerivative_le hF hO hD) hf hdf hcjet.1 hcjet.2
  have hRaise := norm_scalar_frame_contraction_bounds (balancedRaising hF hO hD) g hg L lam k l
    (normalizedPrincipalDerivative g L lam δ R p h k i j) hc x 4 M C1 (D*C1+C2)
    (actualBeta g L lam δ R p x) eps (by norm_num) (by linarith) hC1.le (by positivity) heps hb
    (fun b => (norm_balancedRaising_le hF hO hD b).trans (by norm_num)) hf hdf hcjet.1 hcjet.2
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [normalizedFirstPrincipalLowering,show (3 : ℝ)*4=12 by norm_num] using hLower.1
  · simpa only [normalizedFirstPrincipalRaising,show (3 : ℝ)*4=12 by norm_num] using hRaise.1
  · change ‖directionalFDeriv (coordinateDirection l)
      (normalizedFirstPrincipalLowering hF hO hD g L lam δ R p h k i j) x‖ ≤ _
    calc
      _ ≤ 3 * 4 * M * ((D*C1+C2)+C1) * eps * actualBeta g L lam δ R p x := hLower.2
      _ = _ := by ring
  · change ‖directionalFDeriv (coordinateDirection l)
      (normalizedFirstPrincipalRaising hF hO hD g L lam δ R p h k i j) x‖ ≤ _
    calc
      _ ≤ 3 * 4 * M * ((D*C1+C2)+C1) * eps * actualBeta g L lam δ R p x := hRaise.2
      _ = _ := by ring

lemma frame_shift_inner_adjoint (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (c : Fin 3 → ℝ) (u v : SphereL2) (du rv : Fin 3 → SphereL2)
    (hdu : ∀ i, (u,du i) ∈ sphereDerivativeGraph hF hO hD i)
    (hrv : ∀ i, (v,rv i) ∈ sphereRaisingGraph hF hO hD i) :
    ⟪∑ i, c i • du i,v⟫_ℝ = ⟪u,∑ i, c i • rv i⟫_ℝ := by
  rw [sum_inner,inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_smul_left,real_inner_smul_right]
  rw [sphereDerivativeGraph_inner_adjoint hF hO hD i u (du i) v (rv i) (hdu i) (hrv i)]

lemma normalizedFirstPrincipalLowering_graph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (k i j : Fin 3) (x : R3) (u U : SphereL2) (v : Fin 3 → SphereL2)
    (hU : (u,U) ∈ sphereBesselGraph hO hD (1/2 : ℝ))
    (hv : ∀ b, (u,v b) ∈ sphereDerivativeGraph hF hO hD b) :
    (normalizedPrincipalDerivative g L lam δ R p h k i j x •
        (-(∑ b, frameEntry g L b k (lam,x) • v b)),
      normalizedFirstPrincipalLowering hF hO hD g L lam δ R p h k i j x U) ∈
        sphereBesselGraph hO hD (-(1/2 : ℝ)) := by
  have he := balancedDerivativeCombination_of_graph hF hO hD
    (fun b => frameEntry g L b k (lam,x)) u U v hU hv
  have hq := halfDegreeMultiplier_graph hO hD
    (normalizedPrincipalDerivative g L lam δ R p h k i j x •
      (-(∑ b, frameEntry g L b k (lam,x) • v b)))
  change (normalizedPrincipalDerivative g L lam δ R p h k i j x •
      (-(∑ b, frameEntry g L b k (lam,x) • v b)),
    normalizedPrincipalDerivative g L lam δ R p h k i j x •
      (-balancedDerivativeCombination hF hO hD (fun b => frameEntry g L b k (lam,x)) U)) ∈ _
  rw [he]
  simpa only [map_smul,map_neg] using hq

lemma normalizedFirstPrincipalRaising_graph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (k i j : Fin 3) (x : R3) (u U : SphereL2) (v : Fin 3 → SphereL2)
    (hU : (u,U) ∈ sphereBesselGraph hO hD (1/2 : ℝ))
    (hv : ∀ b, (u,v b) ∈ sphereRaisingGraph hF hO hD b) :
    (normalizedPrincipalDerivative g L lam δ R p h k i j x •
        (-(∑ b, frameEntry g L b k (lam,x) • v b)),
      normalizedFirstPrincipalRaising hF hO hD g L lam δ R p h k i j x U) ∈
        sphereBesselGraph hO hD (-(1/2 : ℝ)) := by
  have he := balancedRaisingCombination_of_graph hF hO hD
    (fun b => frameEntry g L b k (lam,x)) u U v hU hv
  have hq := halfDegreeMultiplier_graph hO hD
    (normalizedPrincipalDerivative g L lam δ R p h k i j x •
      (-(∑ b, frameEntry g L b k (lam,x) • v b)))
  change (normalizedPrincipalDerivative g L lam δ R p h k i j x •
      (-(∑ b, frameEntry g L b k (lam,x) • v b)),
    normalizedPrincipalDerivative g L lam δ R p h k i j x •
      (-balancedRaisingCombination hF hO hD (fun b => frameEntry g L b k (lam,x)) U)) ∈ _
  rw [he]
  simpa only [map_smul,map_neg] using hq

lemma directional_const_clm_apply {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] F) (X : R3) (u : R3 → E) (hu : ContDiff ℝ ∞ u) (x : R3) :
    directionalFDeriv X (fun y => T (u y)) x = T (directionalFDeriv X u x) := by
  unfold directionalFDeriv
  have he := (T.hasFDerivAt.comp x (hu.differentiable (by simp) x).hasFDerivAt).fderiv
  change (fderiv ℝ (T ∘ u) x) X = T ((fderiv ℝ u x) X)
  rw [he]
  rfl

lemma directional_sphereDerivativeGraph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (b : Fin 3)
    (X : R3) (u v : R3 → SphereL2) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hgraph : ∀ x, (u x,v x) ∈ sphereDerivativeGraph hF hO hD b) (x : R3) :
    (directionalFDeriv X u x,directionalFDeriv X v x) ∈ sphereDerivativeGraph hF hO hD b := by
  intro m
  have he : (fun y => sphereHarmonicCoordinate hO hD m (v y)) =
      (fun y => HarmonicDerivativeOperator.harmonicDerivative hF m b (sphereHarmonicCoordinate hO hD (m+1) (u y))) :=
    funext (fun y => hgraph y m)
  have hd := congrArg (fun F => directionalFDeriv X F x) he
  rw [directional_const_clm_apply _ X v hv x,
    directional_const_clm_apply _ X (fun y => sphereHarmonicCoordinate hO hD (m+1) (u y))
      ((sphereHarmonicCoordinate hO hD (m+1)).contDiff.comp hu) x,
    directional_const_clm_apply _ X u hu x] at hd
  exact hd

theorem actual_first_principal_ambient_pair (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (k i j : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3)
    (hb : 0 < actualBeta g L lam δ R p x) :
    let a := fun y => actualPrincipalMatrix g L lam δ R p h y i j
    let phi := ambientSphereL2 G hG
    let phiHalf := ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG
    let du := fun b => directionalFDeriv (coordinateDirection i)
      (directionalFDeriv (coordinateDirection j) (ambientDerivativeField hF hO hD b G hG)) x
    ⟪directionalFDeriv (coordinateDirection k) a x •
        (-(∑ b, frameEntry g L b k (lam,x) • du b)),phi x⟫_ℝ =
      (actualBeta g L lam δ R p x)⁻¹ *
        ⟪directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j) phiHalf) x,
          normalizedFirstPrincipalRaising hF hO hD g L lam δ R p h k i j x (phiHalf x)⟫_ℝ := by
  dsimp only
  let a : R3 → ℝ := fun y => actualPrincipalMatrix g L lam δ R p h y i j
  let phi : R3 → SphereL2 := ambientSphereL2 G hG
  let phiHalf : R3 → SphereL2 := ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG
  let u : SphereL2 := directionalFDeriv (coordinateDirection i)
    (directionalFDeriv (coordinateDirection j) phi) x
  let U : SphereL2 := directionalFDeriv (coordinateDirection i)
    (directionalFDeriv (coordinateDirection j) phiHalf) x
  let du : Fin 3 → SphereL2 := fun b => directionalFDeriv (coordinateDirection i)
    (directionalFDeriv (coordinateDirection j) (ambientDerivativeField hF hO hD b G hG)) x
  let rv : Fin 3 → SphereL2 := fun b => ambientRaisingField hF hO hD b G hG x
  let raw : SphereL2 := -(∑ b, frameEntry g L b k (lam,x) • rv b)
  let c : ℝ := normalizedPrincipalDerivative g L lam δ R p h k i j x
  have hphi := contDiff_ambientSphereL2 G hG
  have hhalf := contDiff_ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG
  have hdu (b : Fin 3) : (u,du b) ∈ sphereDerivativeGraph hF hO hD b := by
    apply directional_sphereDerivativeGraph hF hO hD b (coordinateDirection i)
      (directionalFDeriv (coordinateDirection j) phi)
      (directionalFDeriv (coordinateDirection j) (ambientDerivativeField hF hO hD b G hG))
      (contDiff_directionalFDeriv _ _ hphi)
      (contDiff_directionalFDeriv _ _ (contDiff_ambientDerivativeField hF hO hD b G hG))
    intro y
    exact directional_sphereDerivativeGraph hF hO hD b (coordinateDirection j) phi
      (ambientDerivativeField hF hO hD b G hG) hphi
      (contDiff_ambientDerivativeField hF hO hD b G hG)
      (ambientDerivativeField_graph hF hO hD b G hG) y
  have hU : (u,U) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := by
    exact directionalDeriv_besselGraph hO hD (1/2 : ℝ) (coordinateDirection i)
      (directionalFDeriv (coordinateDirection j) phi)
      (directionalFDeriv (coordinateDirection j) phiHalf)
      (contDiff_directionalFDeriv _ _ hphi) (contDiff_directionalFDeriv _ _ hhalf)
      (fun y => directionalDeriv_besselGraph hO hD (1/2 : ℝ) (coordinateDirection j)
        phi phiHalf hphi hhalf (ambientBesselField_graph hO hD (1/2 : ℝ) (by norm_num) G hG) y) x
  have hrv (b : Fin 3) : (phi x,rv b) ∈ sphereRaisingGraph hF hO hD b :=
    ambientRaisingField_graph hF hO hD b G hG x
  have hadj : ⟪-(∑ b, frameEntry g L b k (lam,x) • du b),phi x⟫_ℝ = ⟪u,raw⟫_ℝ := by
    rw [inner_neg_left]
    rw [frame_shift_inner_adjoint hF hO hD _ u (phi x) du rv hdu hrv]
    exact (inner_neg_right _ _).symm
  have hK := normalizedFirstPrincipalRaising_graph hF hO hD g L lam δ R p h k i j x
    (phi x) (phiHalf x) rv (ambientBesselField_graph hO hD (1/2 : ℝ) (by norm_num) G hG x) hrv
  have he : halfDegreeMultiplier hO hD (c • raw) =
      normalizedFirstPrincipalRaising hF hO hD g L lam δ R p h k i j x (phiHalf x) :=
    spectralGraph_output_unique hO hD (besselWeight (-(1/2 : ℝ))) (c • raw) _ _
      (halfDegreeMultiplier_graph hO hD (c • raw)) hK
  have hpair : ⟪u,c • raw⟫_ℝ =
      ⟪U,normalizedFirstPrincipalRaising hF hO hD g L lam δ R p h k i j x (phiHalf x)⟫_ℝ := by
    calc
      ⟪u,c • raw⟫_ℝ = ⟪c • raw,u⟫_ℝ := real_inner_comm (c • raw) u
      _ = ⟪halfDegreeMultiplier hO hD (c • raw),U⟫_ℝ :=
        inner_eq_halfDegreeMultiplier hO hD (c • raw) u U hU
      _ = ⟪normalizedFirstPrincipalRaising hF hO hD g L lam δ R p h k i j x (phiHalf x),U⟫_ℝ := by rw [he]
      _ = ⟪U,normalizedFirstPrincipalRaising hF hO hD g L lam δ R p h k i j x (phiHalf x)⟫_ℝ :=
        real_inner_comm U _
  change ⟪directionalFDeriv (coordinateDirection k) a x •
    (-(∑ b, frameEntry g L b k (lam,x) • du b)),phi x⟫_ℝ = _
  rw [real_inner_smul_left,hadj]
  rw [← hpair,real_inner_smul_right]
  dsimp only [c,normalizedPrincipalDerivative,a]
  field_simp [hb.ne'] <;> ring


end OAI.AnisotropicCalderon.ActualBalancedFirstPrincipalError
