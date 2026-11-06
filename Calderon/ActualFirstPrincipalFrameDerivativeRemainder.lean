import Calderon.ActualSupportLocalSecondForm

noncomputable section
open MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.ActualFirstPrincipalFrameDerivativeRemainder
open SphereHarmonic SpectralCoreRegularity SpectralWeightedGraph AngularShiftGraph
  BalancedAngularShift BalancedFrameAngularShift SmoothMetricFrame
  ReferenceDensityBounds PrincipalCommutator ActualScalarPrincipalAdjoint
  ActualPerturbedDefect PerturbedDensityAdjoint ConformalDepth RadiusProfile
  AmbientAngularShift SmoothSphereFields SmoothAngularApplication SectionFiveErrorForms
  BaseDensityAdjoint WeightedBaseSpectral ActualBalancedFirstPrincipalError
  ActualSupportLocalSecondForm

def harmonicFrameLoweringCoefficient (hF : SphereFischerInner)
    (g : MatrixField) (L lam : ℝ) (k : Fin 3) (m : ℕ) (x : R3) :
    harmonicSphereSubspace (m+1) →L[ℝ] harmonicSphereSubspace m :=
  -(∑ b, frameEntry g L b k (lam,x) • HarmonicDerivativeOperator.harmonicDerivative hF m b)


def firstFrameRaising (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (k q i j : Fin 3) (x : R3) : SphereL2 →L[ℝ] SphereL2 :=
  (actualBeta g L lam δ R p x * actualPrincipalMatrix g L lam δ R p h x i j) •
    (∑ b, familyDirectionalDeriv q (frameEntry g L b k) (lam,x) • balancedRaising hF hO hD b)


def secondFrameRaising (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (k i j : Fin 3) (x : R3) : SphereL2 →L[ℝ] SphereL2 :=
  actualPrincipalMatrix g L lam δ R p h x i j •
    (∑ b, familyDirectionalDeriv i (familyDirectionalDeriv j (frameEntry g L b k)) (lam,x) •
      balancedRaising hF hO hD b)


def firstFrameContribution (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (k q i j l m : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : ℝ :=
  ⟪-(actualPrincipalMatrix g L lam δ R p h x i j •
      (-(∑ b, familyDirectionalDeriv q (frameEntry g L b k) (lam,x) •
        directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection m)
          (ambientDerivativeField hF hO hD b G hG)) x))),ambientSphereL2 G hG x⟫_ℝ


def secondFrameContribution (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (k i j : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : ℝ :=
  ⟪-(actualPrincipalMatrix g L lam δ R p h x i j •
      (-(∑ b, familyDirectionalDeriv i (familyDirectionalDeriv j (frameEntry g L b k)) (lam,x) •
        directionalFDeriv (coordinateDirection k) (ambientDerivativeField hF hO hD b G hG) x))),
    ambientSphereL2 G hG x⟫_ℝ


lemma directional_finite_scalar_contraction {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (X : R3) (c : Fin 3 → R3 → ℝ) (hc : ∀ b, ContDiff ℝ ∞ (c b))
    (S : Fin 3 → V) (x : R3) :
    directionalFDeriv X (fun y => ∑ b, c b y • S b) x =
      ∑ b, directionalFDeriv X (c b) x • S b := by
  classical
  have ht (b : Fin 3) : ContDiff ℝ ∞ (fun y => c b y • S b) := (hc b).smul contDiff_const
  unfold directionalFDeriv
  rw [fderiv_fun_sum (fun b _ => (ht b).differentiable (by simp) x)]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro b _
  have he := directionalFDeriv_smul X (c b) (fun _ => S b) (hc b) contDiff_const x
  simpa only [directionalFDeriv,fderiv_const_apply,zero_apply,smul_zero,add_zero] using he


lemma harmonicFrameLoweringCoefficient_derivatives (hF : SphereFischerInner)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (k i j : Fin 3) (m : ℕ) (x : R3) :
    directionalFDeriv (coordinateDirection j) (harmonicFrameLoweringCoefficient hF g L lam k m) x =
      -(∑ b, familyDirectionalDeriv j (frameEntry g L b k) (lam,x) •
        HarmonicDerivativeOperator.harmonicDerivative hF m b) ∧
    directionalFDeriv (coordinateDirection i)
      (directionalFDeriv (coordinateDirection j) (harmonicFrameLoweringCoefficient hF g L lam k m)) x =
      -(∑ b, familyDirectionalDeriv i (familyDirectionalDeriv j (frameEntry g L b k)) (lam,x) •
        HarmonicDerivativeOperator.harmonicDerivative hF m b) := by
  have hc (b : Fin 3) : ContDiff ℝ ∞ (fun y : R3 => frameEntry g L b k (lam,y)) :=
    (contDiff_frameEntry g hg L b k).comp (contDiff_const.prodMk contDiff_id)
  have hd (b : Fin 3) : ContDiff ℝ ∞ (fun y : R3 => familyDirectionalDeriv j (frameEntry g L b k) (lam,y)) :=
    (contDiff_familyDirectionalDeriv j _ (contDiff_frameEntry g hg L b k)).comp
      (contDiff_const.prodMk contDiff_id)
  have hfirst (y : R3) :
      directionalFDeriv (coordinateDirection j) (harmonicFrameLoweringCoefficient hF g L lam k m) y =
        -(∑ b, familyDirectionalDeriv j (frameEntry g L b k) (lam,y) •
          HarmonicDerivativeOperator.harmonicDerivative hF m b) := by
    change (fderiv ℝ (fun z : R3 => -(∑ b, frameEntry g L b k (lam,z) •
      HarmonicDerivativeOperator.harmonicDerivative hF m b)) y) (coordinateDirection j) = _
    rw [fderiv_fun_neg (𝕜 := ℝ) (x := y) (f := fun z : R3 => ∑ b, frameEntry g L b k (lam,z) •
      HarmonicDerivativeOperator.harmonicDerivative hF m b)]
    change -(directionalFDeriv (coordinateDirection j)
      (fun z : R3 => ∑ b, frameEntry g L b k (lam,z) •
        HarmonicDerivativeOperator.harmonicDerivative hF m b) y) = _
    simpa only [familyDirectionalDeriv] using congrArg Neg.neg
      (directional_finite_scalar_contraction (coordinateDirection j)
        (fun b z => frameEntry g L b k (lam,z)) hc
        (fun b => HarmonicDerivativeOperator.harmonicDerivative hF m b) y)
  refine ⟨hfirst x,?_⟩
  rw [show directionalFDeriv (coordinateDirection j) (harmonicFrameLoweringCoefficient hF g L lam k m) =
      fun y => -(∑ b, familyDirectionalDeriv j (frameEntry g L b k) (lam,y) •
        HarmonicDerivativeOperator.harmonicDerivative hF m b) from funext hfirst]
  change (fderiv ℝ (fun y : R3 => -(∑ b, familyDirectionalDeriv j (frameEntry g L b k) (lam,y) •
    HarmonicDerivativeOperator.harmonicDerivative hF m b)) x) (coordinateDirection i) = _
  rw [fderiv_fun_neg (𝕜 := ℝ) (x := x) (f := fun y : R3 => ∑ b, familyDirectionalDeriv j (frameEntry g L b k) (lam,y) •
    HarmonicDerivativeOperator.harmonicDerivative hF m b)]
  change -(directionalFDeriv (coordinateDirection i)
    (fun y : R3 => ∑ b, familyDirectionalDeriv j (frameEntry g L b k) (lam,y) •
      HarmonicDerivativeOperator.harmonicDerivative hF m b) x) = _
  simpa only [familyDirectionalDeriv] using congrArg Neg.neg
    (directional_finite_scalar_contraction (coordinateDirection i)
      (fun b y => familyDirectionalDeriv j (frameEntry g L b k) (lam,y)) hd
      (fun b => HarmonicDerivativeOperator.harmonicDerivative hF m b) x)


lemma contDiff_firstFrameRaising (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (k q i j : Fin 3) (hL : 0 < L) (hδ : 0 < δ) (hR : 0 < R)
    (hh : ∀ a b, ContDiff ℝ ∞ (fun y => h y a b)) :
    ContDiff ℝ ∞ (firstFrameRaising hF hO hD g L lam δ R p h k q i j) := by
  unfold firstFrameRaising
  apply ContDiff.smul (f := fun x : R3 =>
    actualBeta g L lam δ R p x * actualPrincipalMatrix g L lam δ R p h x i j)
    (g := fun x : R3 => ∑ b, familyDirectionalDeriv q (frameEntry g L b k) (lam,x) •
      balancedRaising hF hO hD b)
  · exact (contDiff_actualBeta g hg L lam δ R p hL hδ hR).mul
      (contDiff_actualPrincipalMatrix_entry g hg L lam δ R p h hδ hR hh i j)
  · apply ContDiff.sum
    intro b _
    exact ((contDiff_familyDirectionalDeriv q _ (contDiff_frameEntry g hg L b k)).comp
      (contDiff_const.prodMk contDiff_id)).smul contDiff_const


lemma contDiff_secondFrameRaising (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (k i j : Fin 3) (hδ : 0 < δ) (hR : 0 < R)
    (hh : ∀ a b, ContDiff ℝ ∞ (fun y => h y a b)) :
    ContDiff ℝ ∞ (secondFrameRaising hF hO hD g L lam δ R p h k i j) := by
  unfold secondFrameRaising
  apply ContDiff.smul (f := fun x : R3 => actualPrincipalMatrix g L lam δ R p h x i j)
    (g := fun x : R3 => ∑ b, familyDirectionalDeriv i (familyDirectionalDeriv j
      (frameEntry g L b k)) (lam,x) • balancedRaising hF hO hD b)
  · exact contDiff_actualPrincipalMatrix_entry g hg L lam δ R p h hδ hR hh i j
  · apply ContDiff.sum
    intro b _
    exact ((contDiff_familyDirectionalDeriv i _
      (contDiff_familyDirectionalDeriv j _ (contDiff_frameEntry g hg L b k))).comp
      (contDiff_const.prodMk contDiff_id)).smul contDiff_const


lemma principal_zero_budget (r q h beta M eps : ℝ)
    (hr : 0 < r) (hM : 1 ≤ M) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hb : 1 ≤ beta) (hsmall : r * beta^2 ≤ eps)
    (hq : |q| ≤ M) (hh : |h| ≤ eps*r) :
    |r*(q+h)| * beta^2 ≤ (M+1)*eps := by
  have hr0 : 0 ≤ r := hr.le
  have hbeta2 : 1 ≤ beta^2 := by nlinarith [sq_nonneg (beta-1)]
  have hre : r ≤ eps := by
    have ht := mul_le_mul_of_nonneg_left hbeta2 hr0
    nlinarith
  have hepr : eps*r ≤ 1 := by nlinarith
  have hsum : |q+h| ≤ M+1 :=
    (abs_add_le q h).trans (add_le_add hq (hh.trans hepr))
  have ha : |r*(q+h)| ≤ r*(M+1) := by
    rw [abs_mul,abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left hsum hr0
  calc
    _ ≤ (r*(M+1))*beta^2 := mul_le_mul_of_nonneg_right ha (sq_nonneg beta)
    _ = (M+1)*(r*beta^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsmall (by linarith)


theorem exists_actual_principal_zero_budget (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ A0 : ℝ, 0 < A0 ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → ∀ R : ℝ, 0 < R → ∀ p : ℕ,
      ∀ x ∈ K, ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ h : MatrixField,
      (∀ i j k l, TwoJetBound (coordinateDirection k) (coordinateDirection l)
        (fun y => h y i j) x (eps * referenceRadius δ R p L x)) →
      1 ≤ actualBeta g L lam δ R p x →
      referenceRadius δ R p L x * actualBeta g L lam δ R p x^2 ≤ eps →
      ∀ i j, |actualPrincipalMatrix g L lam δ R p h x i j| *
        actualBeta g L lam δ R p x^2 ≤ A0*eps := by
  obtain ⟨M,hM,hbackground⟩ := exists_referenceBackground_uniform_two_jet_bound g hg L K hK
  refine ⟨M+1,by linarith,?_⟩
  intro lam hlam δ hδ R hR p x hx eps heps heps1 h hhjet hb hsmall i j
  have hq : |referenceInverseEntryFamily g L i j (lam,x)| ≤ M := by
    simpa only [referenceBackgroundFamily,coordinateJetFamily] using
      hbackground lam hlam x hx (.inr (i,j)) (.inl ())
  have hh : |h x i j| ≤ eps*referenceRadius δ R p L x := (hhjet i j 0 0).1
  simpa only [actualPrincipalMatrix] using principal_zero_budget
    (referenceRadius δ R p L x) (referenceInverseEntryFamily g L i j (lam,x))
    (h x i j) (actualBeta g L lam δ R p x) M eps
    (referenceRadius_pos δ R p L x hδ hR) hM heps heps1 hb hsmall hq hh


lemma beta_principal_value_derivative_budget (beta a : R3 → ℝ)
    (hbeta : ContDiff ℝ ∞ beta) (ha : ContDiff ℝ ∞ a) (l : Fin 3) (x : R3)
    (A0 A1 D eps : ℝ) (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hD : 0 ≤ D) (heps : 0 ≤ eps)
    (hb : 1 ≤ beta x) (ha2 : |a x| * beta x^2 ≤ A0*eps)
    (hDa : |directionalFDeriv (coordinateDirection l) a x| ≤ A1*eps/beta x)
    (hDb : |directionalFDeriv (coordinateDirection l) beta x| ≤ D*beta x^2) :
    |a x| ≤ A0*eps ∧ |beta x*a x| ≤ A0*eps ∧
      |directionalFDeriv (coordinateDirection l) (fun y => beta y*a y) x| ≤
        (D*A0+A1)*eps*beta x := by
  have hbpos : 0 < beta x := lt_of_lt_of_le zero_lt_one hb
  have hbeta2 : 1 ≤ beta x^2 := by nlinarith [sq_nonneg (beta x-1)]
  have hbetasquare : beta x ≤ beta x^2 := by nlinarith [sq_nonneg (beta x-1)]
  have ha0 : |a x| ≤ A0*eps := by
    calc
      _ ≤ |a x| * beta x^2 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hbeta2 (abs_nonneg (a x))
      _ ≤ _ := ha2
  have hc0 : |beta x*a x| ≤ A0*eps := by
    rw [abs_mul,abs_of_pos hbpos]
    calc
      _ ≤ |a x| * beta x^2 := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right hbetasquare (abs_nonneg (a x))
      _ ≤ _ := ha2
  have hterm1 : |directionalFDeriv (coordinateDirection l) beta x*a x| ≤ D*A0*eps := by
    rw [abs_mul]
    calc
      _ ≤ (D*beta x^2)*|a x| := mul_le_mul_of_nonneg_right hDb (abs_nonneg (a x))
      _ = D*(|a x| * beta x^2) := by ring
      _ ≤ D*(A0*eps) := mul_le_mul_of_nonneg_left ha2 hD
      _ = _ := by ring
  have hterm2 : |beta x*directionalFDeriv (coordinateDirection l) a x| ≤ A1*eps := by
    rw [abs_mul,abs_of_pos hbpos]
    simpa only [mul_comm] using (le_div_iff₀ hbpos).mp hDa
  have hcd0 : |directionalFDeriv (coordinateDirection l) (fun y => beta y*a y) x| ≤
      (D*A0+A1)*eps := by
    rw [directional_mul _ beta a hbeta ha x]
    calc
      _ ≤ |directionalFDeriv (coordinateDirection l) beta x*a x| +
        |beta x*directionalFDeriv (coordinateDirection l) a x| := abs_add_le _ _
      _ ≤ D*A0*eps+A1*eps := add_le_add hterm1 hterm2
      _ = _ := by ring
  refine ⟨ha0,hc0,?_⟩
  exact hcd0.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hb
      (show 0 ≤ (D*A0+A1)*eps by positivity))


lemma norm_scalar_contraction_derivative_budget
    (S : Fin 3 → SphereL2 →L[ℝ] SphereL2)
    (f : Fin 3 → R3 → ℝ) (hf : ∀ b, ContDiff ℝ ∞ (f b))
    (c : R3 → ℝ) (hc : ContDiff ℝ ∞ c) (l : Fin 3) (x : R3)
    (B M A E beta eps : ℝ) (hB : 0 ≤ B) (hM : 0 ≤ M) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (heps : 0 ≤ eps) (hb : 1 ≤ beta) (hS : ∀ b, ‖S b‖ ≤ B)
    (hf0 : ∀ b, |f b x| ≤ M)
    (hf1 : ∀ b, |directionalFDeriv (coordinateDirection l) (f b) x| ≤ M)
    (hc0 : |c x| ≤ A*eps)
    (hc1 : |directionalFDeriv (coordinateDirection l) c x| ≤ E*eps*beta) :
    ‖c x • (∑ b, f b x • S b)‖ ≤ 3*B*M*A*eps ∧
    ‖directionalFDeriv (coordinateDirection l) (fun y => c y • (∑ b, f b y • S b)) x‖ ≤
      3*B*M*(E+A)*eps*beta := by
  let F : R3 → SphereL2 →L[ℝ] SphereL2 := fun y => ∑ b, f b y • S b
  have hFsmooth : ContDiff ℝ ∞ F := ContDiff.sum (fun b _ => (hf b).smul contDiff_const)
  have hF : ‖F x‖ ≤ 3*B*M := norm_finite_contraction_le S _ B M hB hM hS hf0
  have hDF : ‖directionalFDeriv (coordinateDirection l) F x‖ ≤ 3*B*M := by
    rw [directional_finite_scalar_contraction (coordinateDirection l) f hf S x]
    exact norm_finite_contraction_le S _ B M hB hM hS hf1
  change ‖c x • F x‖ ≤ _ ∧
    ‖directionalFDeriv (coordinateDirection l) (fun y => c y • F y) x‖ ≤ _
  constructor
  · rw [norm_smul,Real.norm_eq_abs]
    calc
      _ ≤ (A*eps)*(3*B*M) := mul_le_mul hc0 hF (norm_nonneg _) (mul_nonneg hA heps)
      _ = _ := by ring
  · rw [directionalFDeriv_smul _ c F hc hFsmooth x]
    calc
      _ ≤ ‖directionalFDeriv (coordinateDirection l) c x • F x‖ +
          ‖c x • directionalFDeriv (coordinateDirection l) F x‖ := norm_add_le _ _
      _ = |directionalFDeriv (coordinateDirection l) c x| * ‖F x‖ +
          |c x| * ‖directionalFDeriv (coordinateDirection l) F x‖ := by
        simp only [norm_smul,Real.norm_eq_abs]
      _ ≤ (E*eps*beta)*(3*B*M)+(A*eps)*(3*B*M) :=
        add_le_add (mul_le_mul hc1 hF (norm_nonneg _) (by positivity))
          (mul_le_mul hc0 hDF (norm_nonneg _) (mul_nonneg hA heps))
      _ ≤ _ := by
        have ht := mul_le_mul_of_nonneg_left hb (show 0 ≤ 3*B*M*A*eps by positivity)
        nlinarith


theorem exists_actual_frame_uniform_budgets (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ Cw Cdw C2 : ℝ, 0 < Cw ∧ 0 < Cdw ∧ 0 < C2 ∧
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ h : MatrixField,
      (∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) →
      (∀ i j k l, TwoJetBound (coordinateDirection k) (coordinateDirection l)
        (fun y => h y i j) x (eps * referenceRadius δ R p L x)) →
      1 ≤ actualBeta g L lam δ R p x →
      referenceRadius δ R p L x * actualBeta g L lam δ R p x^2 ≤ eps →
      ∀ k q i j l,
        ‖firstFrameRaising hF hO hD g L lam δ R p h k q i j x‖ ≤ Cw*eps ∧
        ‖fderiv ℝ (firstFrameRaising hF hO hD g L lam δ R p h k q i j)
          x (coordinateDirection l)‖ ≤ Cdw*eps*actualBeta g L lam δ R p x ∧
        ‖secondFrameRaising hF hO hD g L lam δ R p h k i j x‖ ≤ C2*eps := by
  obtain ⟨M,hM,hframe⟩ := exists_frameEntry_uniform_two_jet_bound g hg L K hK
  obtain ⟨A0,hA0,hzero⟩ := exists_actual_principal_zero_budget g hg L K hK
  obtain ⟨A1,A2,hA1,hA2,hprincipal⟩ := exists_actual_principal_first_second_bounds g hg L hL K hK
  obtain ⟨D,hDpos,hbetaDer⟩ := exists_dilated_referenceRadius_uniform_beta_derivative_bounds_at g hg K hK L hL
  refine ⟨12*M*A0,12*M*((D+1)*A0+A1),12*M*A0,by positivity,by positivity,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh hhjet hb hsmall k q i j l
  let beta : R3 → ℝ := actualBeta g L lam δ R p
  let a : R3 → ℝ := fun y => actualPrincipalMatrix g L lam δ R p h y i j
  let c : R3 → ℝ := fun y => beta y*a y
  let f : Fin 3 → R3 → ℝ := fun b y => familyDirectionalDeriv q (frameEntry g L b k) (lam,y)
  have hbeta : ContDiff ℝ ∞ beta := contDiff_actualBeta g hg L lam δ R p hL hδ hR
  have ha : ContDiff ℝ ∞ a := contDiff_actualPrincipalMatrix_entry g hg L lam δ R p h hδ hR hh i j
  have hc : ContDiff ℝ ∞ c := hbeta.mul ha
  have hf (b : Fin 3) : ContDiff ℝ ∞ (f b) :=
    (contDiff_familyDirectionalDeriv q _ (contDiff_frameEntry g hg L b k)).comp
      (contDiff_const.prodMk contDiff_id)
  have ha2 : |a x| * beta x^2 ≤ A0*eps :=
    hzero lam hlam δ hδ R hR p x hx eps heps heps1 h hhjet hb hsmall i j
  have hDa : |directionalFDeriv (coordinateDirection l) a x| ≤ A1*eps/beta x :=
    (hprincipal lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh hhjet hb hsmall i j l l).1
  have hDb : |directionalFDeriv (coordinateDirection l) beta x| ≤ D*beta x^2 := by
    have hn : ‖fderiv ℝ beta x‖ ≤ D*beta x^2 := (hbetaDer lam hlam δ hδ hδ1 R hR p hp x hx).1
    have ht := (fderiv ℝ beta x).le_opNorm (coordinateDirection l)
    simpa only [directionalFDeriv,Real.norm_eq_abs,norm_coordinateDirection,mul_one] using
      ht.trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  have hscalar := beta_principal_value_derivative_budget beta a hbeta ha l x
    A0 A1 D eps hA0.le hA1.le hDpos.le heps hb ha2 hDa hDb
  have hf0 (b : Fin 3) : |f b x| ≤ M := hframe lam hlam x hx b k (.inr (.inl q))
  have hf1 (b : Fin 3) : |directionalFDeriv (coordinateDirection l) (f b) x| ≤ M :=
    hframe lam hlam x hx b k (.inr (.inr (q,l)))
  have hS (b : Fin 3) : ‖balancedRaising hF hO hD b‖ ≤ 4 :=
    (norm_balancedRaising_le hF hO hD b).trans (by norm_num)
  have hfirst := norm_scalar_contraction_derivative_budget (balancedRaising hF hO hD)
    f hf c hc l x 4 M A0 (D*A0+A1) (beta x) eps
    (by norm_num) (by linarith) hA0.le (by positivity) heps hb hS hf0 hf1 hscalar.2.1 hscalar.2.2
  refine ⟨?_,?_,?_⟩
  · change ‖c x • (∑ b, f b x • balancedRaising hF hO hD b)‖ ≤ _
    calc
      _ ≤ 3*4*M*A0*eps := hfirst.1
      _ = _ := by ring
  · change ‖directionalFDeriv (coordinateDirection l)
      (firstFrameRaising hF hO hD g L lam δ R p h k q i j) x‖ ≤ _
    calc
      _ ≤ 3*4*M*((D*A0+A1)+A0)*eps*beta x := hfirst.2
      _ = _ := by ring
  · have hsecond : ‖∑ b, familyDirectionalDeriv i (familyDirectionalDeriv j (frameEntry g L b k)) (lam,x) •
        balancedRaising hF hO hD b‖ ≤ 3*4*M :=
      norm_finite_contraction_le (balancedRaising hF hO hD) _ 4 M
        (by norm_num) (by linarith) hS
        (fun b => hframe lam hlam x hx b k (.inr (.inr (j,i))))
    rw [secondFrameRaising,norm_smul,Real.norm_eq_abs]
    calc
      _ ≤ (A0*eps)*(3*4*M) := mul_le_mul hscalar.1 hsecond (norm_nonneg _) (mul_nonneg hA0.le heps)
      _ = _ := by ring


lemma finite_lowering_pair_normalized (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (c : Fin 3 → ℝ) (u U v V : SphereL2) (du rv : Fin 3 → SphereL2)
    (hU : (u,U) ∈ sphereBesselGraph hO hD (1/2 : ℝ))
    (hV : (v,V) ∈ sphereBesselGraph hO hD (1/2 : ℝ))
    (hdu : ∀ b, (u,du b) ∈ sphereDerivativeGraph hF hO hD b)
    (hrv : ∀ b, (v,rv b) ∈ sphereRaisingGraph hF hO hD b) :
    ⟪∑ b, c b • du b,v⟫_ℝ =
      ⟪U,balancedRaisingCombination hF hO hD c V⟫_ℝ := by
  have he := balancedRaisingCombination_of_graph hF hO hD c v V rv hV hrv
  rw [frame_shift_inner_adjoint hF hO hD c u v du rv hdu hrv]
  calc
    ⟪u,∑ b, c b • rv b⟫_ℝ = ⟪∑ b, c b • rv b,u⟫_ℝ :=
      real_inner_comm (∑ b, c b • rv b) u
    _ = ⟪halfDegreeMultiplier hO hD (∑ b, c b • rv b),U⟫_ℝ :=
      inner_eq_halfDegreeMultiplier hO hD _ u U hU
    _ = ⟪balancedRaisingCombination hF hO hD c V,U⟫_ℝ := by rw [← he]
    _ = _ := real_inner_comm U _


lemma firstFrameContribution_eq_normalized (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (k q i j l m : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3)
    (hb : 0 < actualBeta g L lam δ R p x) :
    firstFrameContribution hF hO hD g L lam δ R p h k q i j l m G hG x =
      (actualBeta g L lam δ R p x)⁻¹ *
        ⟪directionalDeriv (coordinateDirection l) (directionalDeriv (coordinateDirection m)
            (ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG)) x,
          firstFrameRaising hF hO hD g L lam δ R p h k q i j x
            (ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG x)⟫_ℝ := by
  let phi : R3 → SphereL2 := ambientSphereL2 G hG
  let phiHalf : R3 → SphereL2 := ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG
  let u : SphereL2 := directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection m) phi) x
  let U : SphereL2 := directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection m) phiHalf) x
  let du : Fin 3 → SphereL2 := fun b => directionalFDeriv (coordinateDirection l)
    (directionalFDeriv (coordinateDirection m) (ambientDerivativeField hF hO hD b G hG)) x
  let rv : Fin 3 → SphereL2 := fun b => ambientRaisingField hF hO hD b G hG x
  let e : Fin 3 → ℝ := fun b => familyDirectionalDeriv q (frameEntry g L b k) (lam,x)
  have hphi : ContDiff ℝ ∞ phi := contDiff_ambientSphereL2 G hG
  have hhalf : ContDiff ℝ ∞ phiHalf := contDiff_ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG
  have hdu (b : Fin 3) : (u,du b) ∈ sphereDerivativeGraph hF hO hD b := by
    apply directional_sphereDerivativeGraph hF hO hD b (coordinateDirection l)
      (directionalFDeriv (coordinateDirection m) phi)
      (directionalFDeriv (coordinateDirection m) (ambientDerivativeField hF hO hD b G hG))
      (contDiff_directionalFDeriv _ _ hphi)
      (contDiff_directionalFDeriv _ _ (contDiff_ambientDerivativeField hF hO hD b G hG))
    intro y
    exact directional_sphereDerivativeGraph hF hO hD b (coordinateDirection m) phi
      (ambientDerivativeField hF hO hD b G hG) hphi
      (contDiff_ambientDerivativeField hF hO hD b G hG)
      (ambientDerivativeField_graph hF hO hD b G hG) y
  have hU : (u,U) ∈ sphereBesselGraph hO hD (1/2 : ℝ) :=
    directionalDeriv_besselGraph hO hD (1/2 : ℝ) (coordinateDirection l)
      (directionalFDeriv (coordinateDirection m) phi) (directionalFDeriv (coordinateDirection m) phiHalf)
      (contDiff_directionalFDeriv _ _ hphi) (contDiff_directionalFDeriv _ _ hhalf)
      (fun y => directionalDeriv_besselGraph hO hD (1/2 : ℝ) (coordinateDirection m)
        phi phiHalf hphi hhalf (ambientBesselField_graph hO hD (1/2 : ℝ) (by norm_num) G hG) y) x
  have hrv (b : Fin 3) : (phi x,rv b) ∈ sphereRaisingGraph hF hO hD b :=
    ambientRaisingField_graph hF hO hD b G hG x
  have hadj := finite_lowering_pair_normalized hF hO hD e u U (phi x) (phiHalf x) du rv
    hU (ambientBesselField_graph hO hD (1/2 : ℝ) (by norm_num) G hG x) hdu hrv
  change ⟪-(actualPrincipalMatrix g L lam δ R p h x i j • (-(∑ b, e b • du b))),phi x⟫_ℝ = _
  rw [smul_neg,neg_neg,real_inner_smul_left,hadj]
  change actualPrincipalMatrix g L lam δ R p h x i j *
      ⟪U,balancedRaisingCombination hF hO hD e (phiHalf x)⟫_ℝ =
    (actualBeta g L lam δ R p x)⁻¹ *
      ⟪U,(actualBeta g L lam δ R p x * actualPrincipalMatrix g L lam δ R p h x i j) •
        balancedRaisingCombination hF hO hD e (phiHalf x)⟫_ℝ
  rw [real_inner_smul_right]
  field_simp [hb.ne'] <;> ring


lemma secondFrameContribution_eq_normalized (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (k i j : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    secondFrameContribution hF hO hD g L lam δ R p h k i j G hG x =
      ⟪directionalDeriv (coordinateDirection k)
          (ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG) x,
        secondFrameRaising hF hO hD g L lam δ R p h k i j x
          (ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG x)⟫_ℝ := by
  let phi : R3 → SphereL2 := ambientSphereL2 G hG
  let phiHalf : R3 → SphereL2 := ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG
  let u : SphereL2 := directionalFDeriv (coordinateDirection k) phi x
  let U : SphereL2 := directionalFDeriv (coordinateDirection k) phiHalf x
  let du : Fin 3 → SphereL2 := fun b => directionalFDeriv (coordinateDirection k)
    (ambientDerivativeField hF hO hD b G hG) x
  let rv : Fin 3 → SphereL2 := fun b => ambientRaisingField hF hO hD b G hG x
  let e : Fin 3 → ℝ := fun b => familyDirectionalDeriv i (familyDirectionalDeriv j (frameEntry g L b k)) (lam,x)
  have hphi : ContDiff ℝ ∞ phi := contDiff_ambientSphereL2 G hG
  have hhalf : ContDiff ℝ ∞ phiHalf := contDiff_ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG
  have hdu (b : Fin 3) : (u,du b) ∈ sphereDerivativeGraph hF hO hD b :=
    directional_sphereDerivativeGraph hF hO hD b (coordinateDirection k) phi
      (ambientDerivativeField hF hO hD b G hG) hphi
      (contDiff_ambientDerivativeField hF hO hD b G hG)
      (ambientDerivativeField_graph hF hO hD b G hG) x
  have hU : (u,U) ∈ sphereBesselGraph hO hD (1/2 : ℝ) :=
    directionalDeriv_besselGraph hO hD (1/2 : ℝ) (coordinateDirection k)
      phi phiHalf hphi hhalf (ambientBesselField_graph hO hD (1/2 : ℝ) (by norm_num) G hG) x
  have hrv (b : Fin 3) : (phi x,rv b) ∈ sphereRaisingGraph hF hO hD b :=
    ambientRaisingField_graph hF hO hD b G hG x
  have hadj := finite_lowering_pair_normalized hF hO hD e u U (phi x) (phiHalf x) du rv
    hU (ambientBesselField_graph hO hD (1/2 : ℝ) (by norm_num) G hG x) hdu hrv
  change ⟪-(actualPrincipalMatrix g L lam δ R p h x i j • (-(∑ b, e b • du b))),phi x⟫_ℝ = _
  rw [smul_neg,neg_neg,real_inner_smul_left,hadj]
  change actualPrincipalMatrix g L lam δ R p h x i j *
      ⟪U,balancedRaisingCombination hF hO hD e (phiHalf x)⟫_ℝ =
    ⟪U,actualPrincipalMatrix g L lam δ R p h x i j •
      balancedRaisingCombination hF hO hD e (phiHalf x)⟫_ℝ
  rw [real_inner_smul_right]


theorem compact_half_first_form_bound_on_support {ι : Type*} [Fintype ι]
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam eps : ℝ) (heps : 0 ≤ eps)
    (directions : ι → R3) (i : ι) (beta : R3 → ℝ) (hpos : ∀ x, 0 < beta x)
    (room : Set R3) (phi phiHalf phiOne phiThree : R3 → SphereL2)
    (hsupport : tsupport phiHalf ⊆ room)
    (hhalf : ∀ x, (phi x,phiHalf x) ∈ sphereBesselGraph hO hD (1/2))
    (hthree : ∀ x, (phi x,phiThree x) ∈ sphereBesselGraph hO hD (3/2))
    (K : R3 → SphereL2 →L[ℝ] SphereL2) (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hKbound : ∀ x ∈ room, ‖K x‖ ≤ Cw*eps)
    (hN : Integrable (fun x => referenceDensityFamily g L (lam,x) *
      sourceNormSquareIntegrand (beta x) (fun k => directionalDeriv (directions k) phi x)
        (phiOne x) (fun k => directionalDeriv (directions k) phiHalf x) (phiThree x))) :
    |∫ x, referenceDensityFamily g L (lam,x) *
      ⟪directionalDeriv (directions i) phiHalf x,K x (phiHalf x)⟫_ℝ| ≤
      eps*Cw*sourceNormSquare g L lam beta (fun x k => directionalDeriv (directions k) phi x)
        phiOne (fun x k => directionalDeriv (directions k) phiHalf x) phiThree := by
  classical
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (lam,x)
  let NN : R3 → ℝ := fun x => sourceNormSquareIntegrand (beta x)
    (fun k => directionalDeriv (directions k) phi x) (phiOne x)
    (fun k => directionalDeriv (directions k) phiHalf x) (phiThree x)
  have hinner (x : R3) :
      |⟪directionalDeriv (directions i) phiHalf x,K x (phiHalf x)⟫_ℝ| ≤ Cw*eps*NN x := by
    by_cases hx : x ∈ room
    · have hhalfthree := norm_bessel_half_le_threehalf hO hD _ _ _ (hhalf x) (hthree x)
      have hproduct : ‖phiHalf x‖*‖directionalDeriv (directions i) phiHalf x‖ ≤ NN x := by
        calc
          _ ≤ ‖phiThree x‖*‖directionalDeriv (directions i) phiHalf x‖ :=
            mul_le_mul_of_nonneg_right hhalfthree (norm_nonneg _)
          _ ≤ (beta x)⁻¹*‖directionalDeriv (directions i) phiHalf x‖^2+beta x*‖phiThree x‖^2 := by
            simpa only [mul_comm] using mul_le_weighted_sq (beta x)
              ‖directionalDeriv (directions i) phiHalf x‖ ‖phiThree x‖ (hpos x)
          _ ≤ (beta x)⁻¹*(∑ k, ‖directionalDeriv (directions k) phiHalf x‖^2)+beta x*‖phiThree x‖^2 :=
            add_le_add (mul_le_mul_of_nonneg_left
              (norm_sq_le_sum (fun k => directionalDeriv (directions k) phiHalf x) i)
              (inv_nonneg.mpr (hpos x).le)) le_rfl
          _ ≤ _ := angular_error_terms_le_sourceNormSquareIntegrand (beta x) _ _ _ _
      have hKapply : ‖K x (phiHalf x)‖ ≤ (Cw*eps)*‖phiHalf x‖ :=
        ((K x).le_opNorm (phiHalf x)).trans
          (mul_le_mul_of_nonneg_right (hKbound x hx) (norm_nonneg _))
      calc
        _ ≤ ‖directionalDeriv (directions i) phiHalf x‖*‖K x (phiHalf x)‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖directionalDeriv (directions i) phiHalf x‖*((Cw*eps)*‖phiHalf x‖) :=
          mul_le_mul_of_nonneg_left hKapply (norm_nonneg _)
        _ = (Cw*eps)*(‖phiHalf x‖*‖directionalDeriv (directions i) phiHalf x‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hproduct (mul_nonneg hCw heps)
    · have hz := directionalDeriv_eq_zero_off_support phiHalf room hsupport (directions i) x hx
      have hNN0 : 0 ≤ NN x := sourceNormSquareIntegrand_nonneg (beta x) (hpos x).le _ _ _ _
      simp only [hz,inner_zero_left,abs_zero]
      positivity
  have hbound (x : R3) :
      ‖mu x * ⟪directionalDeriv (directions i) phiHalf x,K x (phiHalf x)⟫_ℝ‖ ≤
        (Cw*eps)*(mu x*NN x) := by
    have hmu0 : 0 ≤ mu x := (referenceDensityFamily_pos g hg L (lam,x)).le
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hmu0]
    calc
      _ ≤ mu x*(Cw*eps*NN x) := mul_le_mul_of_nonneg_left (hinner x) hmu0
      _ = _ := by ring
  have hint := norm_integral_le_of_norm_le
    (f := fun x => referenceDensityFamily g L (lam,x) *
      ⟪directionalDeriv (directions i) phiHalf x,K x (phiHalf x)⟫_ℝ)
    (hN.const_mul (Cw*eps))
    (Filter.Eventually.of_forall (fun x => by simpa only [mu,NN] using hbound x))
  rw [integral_const_mul] at hint
  rw [sourceNormSquare_eq_density_integral g hg L lam]
  calc
    _ ≤ (Cw*eps)*(∫ x, referenceDensityFamily g L (lam,x) *
        sourceNormSquareIntegrand (beta x) (fun k => directionalDeriv (directions k) phi x)
          (phiOne x) (fun k => directionalDeriv (directions k) phiHalf x) (phiThree x)) := by
      simpa only [Real.norm_eq_abs] using hint
    _ = _ := by ring


theorem exists_actual_frame_support_bounds
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ Cfirst Csecond : ℝ, 0 < Cfirst ∧ 0 < Csecond ∧
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p → ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 →
      ∀ h : MatrixField, (∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) →
      (∀ x ∈ K, ∀ i j k l, TwoJetBound (coordinateDirection k) (coordinateDirection l)
        (fun y => h y i j) x (eps * referenceRadius δ R p L x)) →
      (∀ x ∈ K, 1 ≤ actualBeta g L lam δ R p x) →
      (∀ x ∈ K, referenceRadius δ R p L x * actualBeta g L lam δ R p x^2 ≤ eps) →
      ∀ G : R3 × R3 → ℝ, ∀ hG : ContDiff ℝ ∞ G,
      (∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) →
      ∀ k i j,
      |∫ x, referenceDensityFamily g L (lam,x) *
        secondFrameContribution hF hO hD g L lam δ R p h k i j G hG x| ≤ eps*Csecond*
        sourceNormSquare g L lam (actualBeta g L lam δ R p)
          (fun x k => directionalDeriv (coordinateDirection k) (ambientSphereL2 G hG) x)
          (ambientBesselField hO hD 1 (by norm_num) G hG)
          (fun x k => directionalDeriv (coordinateDirection k)
            (ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG) x)
          (ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG) ∧
      |∫ x, referenceDensityFamily g L (lam,x) *
        firstFrameContribution hF hO hD g L lam δ R p h k j i j i k G hG x| ≤ eps*Cfirst*
        sourceNormSquare g L lam (actualBeta g L lam δ R p)
          (fun x k => directionalDeriv (coordinateDirection k) (ambientSphereL2 G hG) x)
          (ambientBesselField hO hD 1 (by norm_num) G hG)
          (fun x k => directionalDeriv (coordinateDirection k)
            (ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG) x)
          (ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG) ∧
      |∫ x, referenceDensityFamily g L (lam,x) *
        firstFrameContribution hF hO hD g L lam δ R p h k i i j j k G hG x| ≤ eps*Cfirst*
        sourceNormSquare g L lam (actualBeta g L lam δ R p)
          (fun x k => directionalDeriv (coordinateDirection k) (ambientSphereL2 G hG) x)
          (ambientBesselField hO hD 1 (by norm_num) G hG)
          (fun x k => directionalDeriv (coordinateDirection k)
            (ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG) x)
          (ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG) := by
  obtain ⟨Cw,Cdw,C2,hCw,hCdw,hC2,hbudgets⟩ :=
    exists_actual_frame_uniform_budgets hF hO hD g hg L hL K hK
  obtain ⟨Cmu,hCmu,hdensity⟩ := exists_density_directional_bound_on_compact g hg L K hK
  obtain ⟨D,hDpos,hbetaDer⟩ := exists_dilated_referenceRadius_uniform_beta_derivative_bounds_at g hg K hK L hL
  refine ⟨Cw+(Cmu+D)*Cw+Cdw,C2,by positivity,hC2,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 h hh hhjet hb hsmall G hG hz k i j
  let beta : R3 → ℝ := actualBeta g L lam δ R p
  let phi : R3 → SphereL2 := ambientSphereL2 G hG
  let phiHalf : R3 → SphereL2 := ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG
  let phiOne : R3 → SphereL2 := ambientBesselField hO hD 1 (by norm_num) G hG
  let phiThree : R3 → SphereL2 := ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG
  have hbeta : ContDiff ℝ ∞ beta := contDiff_actualBeta g hg L lam δ R p hL hδ hR
  have hpos (x : R3) : 0 < beta x := actualBeta_pos g hg L lam δ R p hL hδ hR hp x
  have hhalfSmooth : ContDiff ℝ ∞ phiHalf :=
    contDiff_ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG
  have hhalfCompact : HasCompactSupport phiHalf :=
    hasCompactSupport_ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG K hK hz
  have hhalfSupport : tsupport phiHalf ⊆ K :=
    tsupport_ambientBesselField_subset hO hD (1/2 : ℝ) (by norm_num) G hG K hK hz
  have hN : Integrable (fun x => referenceDensityFamily g L (lam,x) *
      sourceNormSquareIntegrand (beta x) (fun l => directionalDeriv (coordinateDirection l) phi x)
        (phiOne x) (fun l => directionalDeriv (coordinateDirection l) phiHalf x) (phiThree x)) :=
    integrable_ambient_source_norm_on_compact hO hD g hg L lam beta hbeta.continuous hpos G hG K hK hz
  have hdbeta (l : Fin 3) (x : R3) (hx : x ∈ K) :
      |directionalDeriv (coordinateDirection l) beta x| ≤ D*beta x^2 := by
    have hn : ‖fderiv ℝ beta x‖ ≤ D*beta x^2 := (hbetaDer lam hlam δ hδ hδ1 R hR p hp x hx).1
    have ht := (fderiv ℝ beta x).le_opNorm (coordinateDirection l)
    simpa only [directionalDeriv,Real.norm_eq_abs,norm_coordinateDirection,mul_one] using
      ht.trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  have hfirstBound (k q i j l m : Fin 3) :
      |∫ x, referenceDensityFamily g L (lam,x) *
        firstFrameContribution hF hO hD g L lam δ R p h k q i j l m G hG x| ≤
      eps*(Cw+(Cmu+D)*Cw+Cdw)*sourceNormSquare g L lam beta
        (fun x b => directionalDeriv (coordinateDirection b) phi x) phiOne
        (fun x b => directionalDeriv (coordinateDirection b) phiHalf x) phiThree := by
    let KK : R3 → SphereL2 →L[ℝ] SphereL2 := firstFrameRaising hF hO hD g L lam δ R p h k q i j
    have hKK : ContDiff ℝ ∞ KK := contDiff_firstFrameRaising hF hO hD g hg L lam δ R p h k q i j hL hδ hR hh
    have hKb (x : R3) (hx : x ∈ K) : ‖KK x‖ ≤ Cw*eps :=
      (hbudgets lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh (hhjet x hx)
        (hb x hx) (hsmall x hx) k q i j l).1
    have hDKb (x : R3) (hx : x ∈ K) :
        ‖fderiv ℝ KK x (coordinateDirection l)‖ ≤ Cdw*eps*beta x :=
      (hbudgets lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh (hhjet x hx)
        (hb x hx) (hsmall x hx) k q i j l).2.1
    have hestimate := compact_normalized_half_second_form_bound_on_support hO hD g hg L lam eps heps
      coordinateDirection l m beta hbeta hpos K hb phi phiHalf phiOne phiThree hhalfSmooth
      hhalfCompact hhalfSupport
      (ambientBesselField_graph hO hD (1/2 : ℝ) (by norm_num) G hG)
      (ambientBesselField_graph hO hD (3/2 : ℝ) (by norm_num) G hG)
      KK hKK Cmu D Cw Cdw hCmu.le hDpos.le hCw.le hCdw.le hKb hDKb
      (fun x hx => hdensity lam hlam x hx l) (hdbeta l) hN
    calc
      _ = |∫ x, referenceDensityFamily g L (lam,x) * (beta x)⁻¹ *
          ⟪directionalDeriv (coordinateDirection l) (directionalDeriv (coordinateDirection m) phiHalf) x,
            KK x (phiHalf x)⟫_ℝ| := by
        congr 1
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by
          change referenceDensityFamily g L (lam,x) *
              firstFrameContribution hF hO hD g L lam δ R p h k q i j l m G hG x =
            referenceDensityFamily g L (lam,x) * (beta x)⁻¹ *
              ⟪directionalDeriv (coordinateDirection l) (directionalDeriv (coordinateDirection m) phiHalf) x,
                KK x (phiHalf x)⟫_ℝ
          rw [firstFrameContribution_eq_normalized hF hO hD g L lam δ R p h k q i j l m G hG x (hpos x)]
          dsimp only [beta,KK,phiHalf]
          ring)
      _ ≤ _ := hestimate
  have hsecondBound (k i j : Fin 3) :
      |∫ x, referenceDensityFamily g L (lam,x) *
        secondFrameContribution hF hO hD g L lam δ R p h k i j G hG x| ≤
      eps*C2*sourceNormSquare g L lam beta
        (fun x b => directionalDeriv (coordinateDirection b) phi x) phiOne
        (fun x b => directionalDeriv (coordinateDirection b) phiHalf x) phiThree := by
    let KK : R3 → SphereL2 →L[ℝ] SphereL2 := secondFrameRaising hF hO hD g L lam δ R p h k i j
    have hKb (x : R3) (hx : x ∈ K) : ‖KK x‖ ≤ C2*eps :=
      (hbudgets lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh (hhjet x hx)
        (hb x hx) (hsmall x hx) k 0 i j 0).2.2
    have hestimate := compact_half_first_form_bound_on_support hO hD g hg L lam eps heps
      coordinateDirection k beta hpos K phi phiHalf phiOne phiThree hhalfSupport
      (ambientBesselField_graph hO hD (1/2 : ℝ) (by norm_num) G hG)
      (ambientBesselField_graph hO hD (3/2 : ℝ) (by norm_num) G hG)
      KK C2 hC2.le hKb hN
    calc
      _ = |∫ x, referenceDensityFamily g L (lam,x) *
          ⟪directionalDeriv (coordinateDirection k) phiHalf x,KK x (phiHalf x)⟫_ℝ| := by
        congr 1
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by
          simpa only [KK,phiHalf] using congrArg (fun z : ℝ => referenceDensityFamily g L (lam,x)*z)
            (secondFrameContribution_eq_normalized hF hO hD g L lam δ R p h k i j G hG x))
      _ ≤ _ := hestimate
  exact ⟨hsecondBound k i j,hfirstBound k j i j i k,hfirstBound k i i j j k⟩


theorem exists_actual_frame_sum_support_bound
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p → ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 →
      ∀ h : MatrixField, (∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) →
      (∀ x ∈ K, ∀ i j k l, TwoJetBound (coordinateDirection k) (coordinateDirection l)
        (fun y => h y i j) x (eps * referenceRadius δ R p L x)) →
      (∀ x ∈ K, 1 ≤ actualBeta g L lam δ R p x) →
      (∀ x ∈ K, referenceRadius δ R p L x * actualBeta g L lam δ R p x^2 ≤ eps) →
      ∀ G : R3 × R3 → ℝ, ∀ hG : ContDiff ℝ ∞ G,
      (∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) →
      |∑ t : Fin 3 × Fin 3 × Fin 3,
        ((∫ x, referenceDensityFamily g L (lam,x) *
          secondFrameContribution hF hO hD g L lam δ R p h t.1 t.2.1 t.2.2 G hG x) +
         (∫ x, referenceDensityFamily g L (lam,x) *
          firstFrameContribution hF hO hD g L lam δ R p h t.1 t.2.2 t.2.1 t.2.2 t.2.1 t.1 G hG x) +
         (∫ x, referenceDensityFamily g L (lam,x) *
          firstFrameContribution hF hO hD g L lam δ R p h t.1 t.2.1 t.2.1 t.2.2 t.2.2 t.1 G hG x))| ≤
        eps*C*sourceNormSquare g L lam (actualBeta g L lam δ R p)
          (fun x k => directionalDeriv (coordinateDirection k) (ambientSphereL2 G hG) x)
          (ambientBesselField hO hD 1 (by norm_num) G hG)
          (fun x k => directionalDeriv (coordinateDirection k)
            (ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG) x)
          (ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG) := by
  classical
  obtain ⟨Cfirst,Csecond,hCfirst,hCsecond,hbounds⟩ := exists_actual_frame_support_bounds hF hO hD g hg L hL K hK
  refine ⟨27*(Csecond+2*Cfirst),by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 h hh hhjet hb hsmall G hG hz
  let n : ℝ := sourceNormSquare g L lam (actualBeta g L lam δ R p)
    (fun x k => directionalDeriv (coordinateDirection k) (ambientSphereL2 G hG) x)
    (ambientBesselField hO hD 1 (by norm_num) G hG)
    (fun x k => directionalDeriv (coordinateDirection k) (ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG) x)
    (ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG)
  let B0 : Fin 3 × Fin 3 × Fin 3 → ℝ := fun t => ∫ x, referenceDensityFamily g L (lam,x) *
    secondFrameContribution hF hO hD g L lam δ R p h t.1 t.2.1 t.2.2 G hG x
  let B1 : Fin 3 × Fin 3 × Fin 3 → ℝ := fun t => ∫ x, referenceDensityFamily g L (lam,x) *
    firstFrameContribution hF hO hD g L lam δ R p h t.1 t.2.2 t.2.1 t.2.2 t.2.1 t.1 G hG x
  let B2 : Fin 3 × Fin 3 × Fin 3 → ℝ := fun t => ∫ x, referenceDensityFamily g L (lam,x) *
    firstFrameContribution hF hO hD g L lam δ R p h t.1 t.2.1 t.2.1 t.2.2 t.2.2 t.1 G hG x
  have hcomponent (t : Fin 3 × Fin 3 × Fin 3) : |B0 t+B1 t+B2 t| ≤ eps*(Csecond+2*Cfirst)*n := by
    obtain ⟨h0,h1,h2⟩ := hbounds lam hlam δ hδ hδ1 R hR p hp eps heps heps1 h hh hhjet hb hsmall G hG hz
      t.1 t.2.1 t.2.2
    calc
      _ ≤ |B0 t+B1 t|+|B2 t| := abs_add_le _ _
      _ ≤ (|B0 t|+|B1 t|)+|B2 t| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ (eps*Csecond*n+eps*Cfirst*n)+eps*Cfirst*n := add_le_add (add_le_add h0 h1) h2
      _ = _ := by ring
  change |∑ t : Fin 3 × Fin 3 × Fin 3, (B0 t+B1 t+B2 t)| ≤ eps*(27*(Csecond+2*Cfirst))*n
  calc
    _ ≤ ∑ t : Fin 3 × Fin 3 × Fin 3, |B0 t+B1 t+B2 t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t : Fin 3 × Fin 3 × Fin 3, eps*(Csecond+2*Cfirst)*n :=
      Finset.sum_le_sum (fun t _ => hcomponent t)
    _ = _ := by norm_num <;> ring


end OAI.AnisotropicCalderon.ActualFirstPrincipalFrameDerivativeRemainder
