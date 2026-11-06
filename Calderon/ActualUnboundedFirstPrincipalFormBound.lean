import Calderon.ActualUnboundedFirstPrincipalNormalForm

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.ActualUnboundedFirstPrincipalFormBound
open SphereHarmonic SpectralCoreRegularity SpectralWeightedGraph AngularShiftGraph
  ReferenceDensityBounds PrincipalCommutator ScalarBaseAdjoint NaturalAngularAdjoint
  ActualScalarPrincipalAdjoint ActualBalancedFirstPrincipalError ActualSupportLocalSecondForm
  ActualFirstPrincipalFrameDerivativeRemainder AmbientAngularShift SmoothSphereFields
  SmoothAngularApplication BaseDensityAdjoint SectionFiveErrorForms
  ActualUnboundedFirstPrincipalNormalForm
  PerturbedDensityAdjoint ConformalDepth RadiusProfile

/-- The original raw first-base evaluation uses genuine unbounded graph
outputs before the principal operator is inserted. -/
theorem actualFrameFirstBase_graph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (b k : Fin 3) (x : R3) :
    (directionalFDeriv (coordinateDirection k) (ambientSphereL2 G hG) x,
     directionalFDeriv (coordinateDirection k) (ambientDerivativeField hF hO hD b G hG) x) ∈
      sphereDerivativeGraph hF hO hD b :=
  directional_sphereDerivativeGraph hF hO hD b (coordinateDirection k)
    (ambientSphereL2 G hG) (ambientDerivativeField hF hO hD b G hG)
    (contDiff_ambientSphereL2 G hG) (contDiff_ambientDerivativeField hF hO hD b G hG)
    (ambientDerivativeField_graph hF hO hD b G hG) x

lemma contDiff_actualFrameFirstBase (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (actualFrameFirstBase hF hO hD g L lam G hG) :=
  contDiff_contractionFirstBase coordinateDirection (negativeFrameEntry g L lam)
    (fun b => ambientDerivativeField hF hO hD b G hG)
    (contDiff_negativeFrameEntry g hg L lam)
    (fun b => contDiff_ambientDerivativeField hF hO hD b G hG)

lemma contDiff_actualFrameFirstPrincipalCommutator (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hδ : 0 < δ) (hR : 0 < R)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (actualFrameFirstPrincipalCommutator hF hO hD g L lam δ R p h G hG) := by
  have ha := OAI.AnisotropicCalderon.ActualPerturbedDefect.contDiff_actualPrincipalMatrix_entry g hg L lam δ R p h hδ hR hh
  exact (contDiff_contractionFirstBase coordinateDirection (negativeFrameEntry g L lam)
    (fun b => scalarSecondBase coordinateDirection (actualPrincipalMatrix g L lam δ R p h)
      (ambientDerivativeField hF hO hD b G hG))
    (contDiff_negativeFrameEntry g hg L lam)
    (fun b => contDiff_scalarSecondBase coordinateDirection _ _ ha
      (contDiff_ambientDerivativeField hF hO hD b G hG))).sub
    (contDiff_scalarSecondBase coordinateDirection _ _ ha
      (contDiff_actualFrameFirstBase hF hO hD g hg L lam G hG))

lemma integrable_density_pair_of_contDiff (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (u w : R3 → SphereL2) (hu : ContDiff ℝ ∞ u)
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w) :
    Integrable (fun x => referenceDensityFamily g L (lam,x) * ⟪u x,w x⟫_ℝ) := by
  have hm : ContDiff ℝ ∞ (fun x : R3 => referenceDensityFamily g L (lam,x)) :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hi := compact_inner_integrable
    (fun x => referenceDensityFamily g L (lam,x) • u x) w
    (hm.smul hu).continuous hw.continuous hc
  simpa only [real_inner_smul_left] using hi

lemma contDiff_firstPrincipalVector (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hδ : 0 < δ) (hR : 0 < R)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (k i j : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (fun x => directionalFDeriv (coordinateDirection k)
      (fun y => actualPrincipalMatrix g L lam δ R p h y i j) x •
      (-(∑ b, frameEntry g L b k (lam,x) •
        directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j)
          (ambientDerivativeField hF hO hD b G hG)) x))) := by
  have ha := OAI.AnisotropicCalderon.ActualPerturbedDefect.contDiff_actualPrincipalMatrix_entry g hg L lam δ R p h hδ hR hh i j
  apply (contDiff_directionalFDeriv (coordinateDirection k) _ ha).smul
  apply ContDiff.neg
  apply ContDiff.sum
  intro b _
  exact ((contDiff_frameEntry g hg L b k).comp (contDiff_const.prodMk contDiff_id)).smul
    (contDiff_directionalFDeriv (coordinateDirection i) _
      (contDiff_directionalFDeriv (coordinateDirection j) _
        (contDiff_ambientDerivativeField hF hO hD b G hG)))

lemma contDiff_firstFrameVector (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hδ : 0 < δ) (hR : 0 < R)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (k q i j l m : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (fun x => -(actualPrincipalMatrix g L lam δ R p h x i j •
      (-(∑ b, familyDirectionalDeriv q (frameEntry g L b k) (lam,x) •
        directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection m)
          (ambientDerivativeField hF hO hD b G hG)) x)))) := by
  have ha := OAI.AnisotropicCalderon.ActualPerturbedDefect.contDiff_actualPrincipalMatrix_entry g hg L lam δ R p h hδ hR hh i j
  apply ContDiff.neg
  apply ha.smul
  apply ContDiff.neg
  apply ContDiff.sum
  intro b _
  exact ((contDiff_familyDirectionalDeriv q _ (contDiff_frameEntry g hg L b k)).comp
    (contDiff_const.prodMk contDiff_id)).smul
    (contDiff_directionalFDeriv (coordinateDirection l) _
      (contDiff_directionalFDeriv (coordinateDirection m) _
        (contDiff_ambientDerivativeField hF hO hD b G hG)))

lemma contDiff_secondFrameVector (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hδ : 0 < δ) (hR : 0 < R)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (k i j : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (fun x => -(actualPrincipalMatrix g L lam δ R p h x i j •
      (-(∑ b, familyDirectionalDeriv i (familyDirectionalDeriv j (frameEntry g L b k)) (lam,x) •
        directionalFDeriv (coordinateDirection k) (ambientDerivativeField hF hO hD b G hG) x)))) := by
  have ha := OAI.AnisotropicCalderon.ActualPerturbedDefect.contDiff_actualPrincipalMatrix_entry g hg L lam δ R p h hδ hR hh i j
  apply ContDiff.neg
  apply ha.smul
  apply ContDiff.neg
  apply ContDiff.sum
  intro b _
  exact ((contDiff_familyDirectionalDeriv i _
    (contDiff_familyDirectionalDeriv j _ (contDiff_frameEntry g hg L b k))).comp
    (contDiff_const.prodMk contDiff_id)).smul
    (contDiff_directionalFDeriv (coordinateDirection k) _
      (contDiff_ambientDerivativeField hF hO hD b G hG))

lemma integrable_firstPrincipalContribution (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hδ : 0 < δ) (hR : 0 < R)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (K : Set R3) (hK : IsCompact K) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (k i j : Fin 3) :
    Integrable (fun x => referenceDensityFamily g L (lam,x) *
      firstPrincipalContribution hF hO hD g L lam δ R p h k i j G hG x) :=
  integrable_density_pair_of_contDiff g hg L lam _ (ambientSphereL2 G hG)
    (contDiff_firstPrincipalVector hF hO hD g hg L lam δ R p h hδ hR hh k i j G hG)
    (contDiff_ambientSphereL2 G hG) (hasCompactSupport_ambientSphereL2 G hG K hK hz)

lemma integrable_firstFrameContribution (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hδ : 0 < δ) (hR : 0 < R)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (K : Set R3) (hK : IsCompact K) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (k q i j l m : Fin 3) :
    Integrable (fun x => referenceDensityFamily g L (lam,x) *
      firstFrameContribution hF hO hD g L lam δ R p h k q i j l m G hG x) :=
  integrable_density_pair_of_contDiff g hg L lam _ (ambientSphereL2 G hG)
    (contDiff_firstFrameVector hF hO hD g hg L lam δ R p h hδ hR hh k q i j l m G hG)
    (contDiff_ambientSphereL2 G hG) (hasCompactSupport_ambientSphereL2 G hG K hK hz)

lemma integrable_secondFrameContribution (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hδ : 0 < δ) (hR : 0 < R)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (K : Set R3) (hK : IsCompact K) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (k i j : Fin 3) :
    Integrable (fun x => referenceDensityFamily g L (lam,x) *
      secondFrameContribution hF hO hD g L lam δ R p h k i j G hG x) :=
  integrable_density_pair_of_contDiff g hg L lam _ (ambientSphereL2 G hG)
    (contDiff_secondFrameVector hF hO hD g hg L lam δ R p h hδ hR hh k i j G hG)
    (contDiff_ambientSphereL2 G hG) (hasCompactSupport_ambientSphereL2 G hG K hK hz)

/-- Exact integral assembly: all four source contributions are integrable,
so no finite-sum/integral interchange is hidden. -/
theorem actualFrameFirstPrincipal_commutator_integral (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hδ : 0 < δ) (hR : 0 < R)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (K : Set R3) (hK : IsCompact K) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    (∫ x, referenceDensityFamily g L (lam,x) *
      ⟪actualFrameFirstPrincipalCommutator hF hO hD g L lam δ R p h G hG x,
        ambientSphereL2 G hG x⟫_ℝ) =
      (∑ t : Fin 3 × Fin 3 × Fin 3, ∫ x, referenceDensityFamily g L (lam,x) *
        firstPrincipalContribution hF hO hD g L lam δ R p h t.1 t.2.1 t.2.2 G hG x) +
      ∑ t : Fin 3 × Fin 3 × Fin 3,
        ((∫ x, referenceDensityFamily g L (lam,x) *
          secondFrameContribution hF hO hD g L lam δ R p h t.1 t.2.1 t.2.2 G hG x) +
         (∫ x, referenceDensityFamily g L (lam,x) *
          firstFrameContribution hF hO hD g L lam δ R p h t.1 t.2.2 t.2.1 t.2.2 t.2.1 t.1 G hG x) +
         (∫ x, referenceDensityFamily g L (lam,x) *
          firstFrameContribution hF hO hD g L lam δ R p h t.1 t.2.1 t.2.1 t.2.2 t.2.2 t.1 G hG x)) := by
  classical
  let f0 : (Fin 3 × Fin 3 × Fin 3) → R3 → ℝ := fun t x => referenceDensityFamily g L (lam,x) *
    firstPrincipalContribution hF hO hD g L lam δ R p h t.1 t.2.1 t.2.2 G hG x
  let f1 : (Fin 3 × Fin 3 × Fin 3) → R3 → ℝ := fun t x => referenceDensityFamily g L (lam,x) *
    secondFrameContribution hF hO hD g L lam δ R p h t.1 t.2.1 t.2.2 G hG x
  let f2 : (Fin 3 × Fin 3 × Fin 3) → R3 → ℝ := fun t x => referenceDensityFamily g L (lam,x) *
    firstFrameContribution hF hO hD g L lam δ R p h t.1 t.2.2 t.2.1 t.2.2 t.2.1 t.1 G hG x
  let f3 : (Fin 3 × Fin 3 × Fin 3) → R3 → ℝ := fun t x => referenceDensityFamily g L (lam,x) *
    firstFrameContribution hF hO hD g L lam δ R p h t.1 t.2.1 t.2.1 t.2.2 t.2.2 t.1 G hG x
  have hi0 (t : Fin 3 × Fin 3 × Fin 3) : Integrable (f0 t) :=
    integrable_firstPrincipalContribution hF hO hD g hg L lam δ R p h hδ hR hh K hK G hG hz t.1 t.2.1 t.2.2
  have hi1 (t : Fin 3 × Fin 3 × Fin 3) : Integrable (f1 t) :=
    integrable_secondFrameContribution hF hO hD g hg L lam δ R p h hδ hR hh K hK G hG hz t.1 t.2.1 t.2.2
  have hi2 (t : Fin 3 × Fin 3 × Fin 3) : Integrable (f2 t) :=
    integrable_firstFrameContribution hF hO hD g hg L lam δ R p h hδ hR hh K hK G hG hz
      t.1 t.2.2 t.2.1 t.2.2 t.2.1 t.1
  have hi3 (t : Fin 3 × Fin 3 × Fin 3) : Integrable (f3 t) :=
    integrable_firstFrameContribution hF hO hD g hg L lam δ R p h hδ hR hh K hK G hG hz
      t.1 t.2.1 t.2.1 t.2.2 t.2.2 t.1
  have he : (∫ x, referenceDensityFamily g L (lam,x) *
      ⟪actualFrameFirstPrincipalCommutator hF hO hD g L lam δ R p h G hG x,
        ambientSphereL2 G hG x⟫_ℝ) =
      ∫ x, ∑ t : Fin 3 × Fin 3 × Fin 3, (f0 t x+f1 t x+f2 t x+f3 t x) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      dsimp only
      rw [actualFrameFirstPrincipal_commutator_pair hF hO hD g hg L lam δ R p h hδ hR hh G hG x]
      simp only [Finset.mul_sum,f0,f1,f2,f3,mul_add])
  rw [he]
  have hsum : (∫ x, ∑ t : Fin 3 × Fin 3 × Fin 3,
      (f0 t x+f1 t x+f2 t x+f3 t x)) =
      ∑ t : Fin 3 × Fin 3 × Fin 3, ∫ x, (f0 t x+f1 t x+f2 t x+f3 t x) := by
    simpa only [Pi.add_apply] using
      (integral_finsetSum Finset.univ
        (f := fun t => f0 t + f1 t + f2 t + f3 t)
        (fun t _ => (((hi0 t).add (hi1 t)).add (hi2 t)).add (hi3 t)))
  rw [hsum]
  have ht (t : Fin 3 × Fin 3 × Fin 3) :
      (∫ x, f0 t x+f1 t x+f2 t x+f3 t x) =
        (∫ x, f0 t x)+(∫ x, f1 t x)+(∫ x, f2 t x)+(∫ x, f3 t x) := by
    have h01 := integral_add (hi0 t) (hi1 t)
    have h012 := integral_add ((hi0 t).add (hi1 t)) (hi2 t)
    have h0123 := integral_add (((hi0 t).add (hi1 t)).add (hi2 t)) (hi3 t)
    simp only [Pi.add_apply] at h012 h0123
    rw [h0123,h012,h01]
  simp_rw [ht]
  change (∑ t : Fin 3 × Fin 3 × Fin 3,
    ((∫ x, f0 t x)+(∫ x, f1 t x)+(∫ x, f2 t x)+(∫ x, f3 t x))) =
    (∑ t : Fin 3 × Fin 3 × Fin 3, ∫ x, f0 t x) +
      ∑ t : Fin 3 × Fin 3 × Fin 3, ((∫ x, f1 t x)+(∫ x, f2 t x)+(∫ x, f3 t x))
  simp only [Finset.sum_add_distrib]
  abel

/-- The fixed-support form bound for the actual raw first-principal
commutator, with exactly the source graph/jet/profile hypotheses. This is one
summand of the full Section 5 commutator, not a full coercivity result. -/
theorem exists_actualFrameFirstPrincipal_commutator_support_bound
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
      |∫ x, referenceDensityFamily g L (lam,x) *
        ⟪actualFrameFirstPrincipalCommutator hF hO hD g L lam δ R p h G hG x,
          ambientSphereL2 G hG x⟫_ℝ| ≤ eps*C*
        sourceNormSquare g L lam (actualBeta g L lam δ R p)
          (fun x k => directionalDeriv (coordinateDirection k) (ambientSphereL2 G hG) x)
          (ambientBesselField hO hD 1 (by norm_num) G hG)
          (fun x k => directionalDeriv (coordinateDirection k)
            (ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG) x)
          (ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG) := by
  obtain ⟨C0,hC0,hbound0⟩ := exists_actual_first_principal_sum_support_bound hF hO hD g hg L hL K hK
  obtain ⟨Cframe,hCframe,hboundFrame⟩ := exists_actual_frame_sum_support_bound hF hO hD g hg L hL K hK
  refine ⟨C0+Cframe,add_pos hC0 hCframe,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 h hh hhjet hb hsmall G hG hz
  have h0 := hbound0 lam hlam δ hδ hδ1 R hR p hp eps heps heps1 h hh hhjet hb hsmall G hG hz
  have hf := hboundFrame lam hlam δ hδ hδ1 R hR p hp eps heps heps1 h hh hhjet hb hsmall G hG hz
  rw [actualFrameFirstPrincipal_commutator_integral hF hO hD g hg L lam δ R p h hδ hR hh K hK G hG hz]
  calc
    _ ≤ |∑ t : Fin 3 × Fin 3 × Fin 3, ∫ x, referenceDensityFamily g L (lam,x) *
        firstPrincipalContribution hF hO hD g L lam δ R p h t.1 t.2.1 t.2.2 G hG x| +
      |∑ t : Fin 3 × Fin 3 × Fin 3,
        ((∫ x, referenceDensityFamily g L (lam,x) *
          secondFrameContribution hF hO hD g L lam δ R p h t.1 t.2.1 t.2.2 G hG x) +
         (∫ x, referenceDensityFamily g L (lam,x) *
          firstFrameContribution hF hO hD g L lam δ R p h t.1 t.2.2 t.2.1 t.2.2 t.2.1 t.1 G hG x) +
         (∫ x, referenceDensityFamily g L (lam,x) *
          firstFrameContribution hF hO hD g L lam δ R p h t.1 t.2.1 t.2.1 t.2.2 t.2.2 t.1 G hG x))| := abs_add_le _ _
    _ ≤ eps*C0*sourceNormSquare g L lam (actualBeta g L lam δ R p)
          (fun x k => directionalDeriv (coordinateDirection k) (ambientSphereL2 G hG) x)
          (ambientBesselField hO hD 1 (by norm_num) G hG)
          (fun x k => directionalDeriv (coordinateDirection k)
            (ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG) x)
          (ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG) +
        eps*Cframe*sourceNormSquare g L lam (actualBeta g L lam δ R p)
          (fun x k => directionalDeriv (coordinateDirection k) (ambientSphereL2 G hG) x)
          (ambientBesselField hO hD 1 (by norm_num) G hG)
          (fun x k => directionalDeriv (coordinateDirection k)
            (ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG) x)
          (ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG) := add_le_add h0 hf
    _ = _ := by ring

end OAI.AnisotropicCalderon.ActualUnboundedFirstPrincipalFormBound
