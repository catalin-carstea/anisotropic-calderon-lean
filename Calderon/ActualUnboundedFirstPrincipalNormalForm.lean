import Calderon.ActualFirstPrincipalFrameDerivativeRemainder

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.ActualUnboundedFirstPrincipalNormalForm
open SphereHarmonic SpectralCoreRegularity SpectralWeightedGraph AngularShiftGraph
  ReferenceDensityBounds PrincipalCommutator ScalarBaseAdjoint NaturalAngularAdjoint
  ActualScalarPrincipalAdjoint ActualBalancedFirstPrincipalError ActualSupportLocalSecondForm
  ActualFirstPrincipalFrameDerivativeRemainder AmbientAngularShift SmoothSphereFields
  SmoothAngularApplication

/-- All angular differentiation is carried by the already constructed graph
outputs `d b`. The coefficients in this auxiliary operator are real scalars. -/
def scalarFirstBase (v : Fin 3 → R3) (c : Fin 3 → R3 → ℝ)
    (u : R3 → SphereL2) (x : R3) : SphereL2 :=
  ∑ k, c k x • directionalFDeriv (v k) u x

def scalarFirstPrincipalRemainder (v : Fin 3 → R3) (a : MatrixField)
    (c : Fin 3 → R3 → ℝ) (u : R3 → SphereL2) (x : R3) : SphereL2 :=
  ∑ k, ∑ i, ∑ j,
    (directionalFDeriv (v k) (fun y => a y i j) x •
       (c k x • directionalFDeriv (v i) (directionalFDeriv (v j) u) x) -
     a x i j • (directionalFDeriv (v i) (directionalFDeriv (v j) (c k)) x •
       directionalFDeriv (v k) u x) -
     a x i j • (directionalFDeriv (v j) (c k) x •
       directionalFDeriv (v i) (directionalFDeriv (v k) u) x) -
     a x i j • (directionalFDeriv (v i) (c k) x •
       directionalFDeriv (v j) (directionalFDeriv (v k) u) x))

lemma contDiff_scalarFirstBase (v : Fin 3 → R3) (c : Fin 3 → R3 → ℝ)
    (u : R3 → SphereL2) (hc : ∀ k, ContDiff ℝ ∞ (c k))
    (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (scalarFirstBase v c u) :=
  ContDiff.sum (fun k _ => (hc k).smul (contDiff_directionalFDeriv (v k) u hu))

/-- Scalar product rules give third-base cancellation on the output field of
an unbounded angular graph. This lemma does not operate raw A on all L². -/
lemma scalar_directional_first_principal_commutator (i j k : R3) (a c : R3 → ℝ)
    (u : R3 → SphereL2) (ha : ContDiff ℝ ∞ a) (hc : ContDiff ℝ ∞ c)
    (hu : ContDiff ℝ ∞ u) (x : R3) :
    c x • directionalFDeriv k (fun y => a y •
      directionalFDeriv i (directionalFDeriv j u) y) x -
      a x • directionalFDeriv i (directionalFDeriv j
        (fun y => c y • directionalFDeriv k u y)) x =
    directionalFDeriv k a x • (c x • directionalFDeriv i (directionalFDeriv j u) x) -
      a x • (directionalFDeriv i (directionalFDeriv j c) x • directionalFDeriv k u x) -
      a x • (directionalFDeriv j c x • directionalFDeriv i (directionalFDeriv k u) x) -
      a x • (directionalFDeriv i c x • directionalFDeriv j (directionalFDeriv k u) x) := by
  rw [directionalFDeriv_smul k a _ ha
    (contDiff_directionalFDeriv i _ (contDiff_directionalFDeriv j u hu)),
    directionalFDeriv_second_smul j i c _ hc (contDiff_directionalFDeriv k u hu),
    directionalFDeriv_third_commute i j k u hu]
  module

lemma scalarSecondBase_fintype_sum {ι : Type*} [Fintype ι]
    (v : Fin 3 → R3) (a : MatrixField) (u : ι → R3 → SphereL2)
    (hu : ∀ b, ContDiff ℝ ∞ (u b)) (x : R3) :
    scalarSecondBase v a (fun y => ∑ b, u b y) x =
      ∑ b, scalarSecondBase v a (u b) x := by
  classical
  unfold scalarSecondBase
  simp_rw [directionalFDeriv_second_fintype_sum _ _ u hu x, Finset.smul_sum]
  calc
    _ = ∑ i : Fin 3, ∑ b : ι, ∑ j : Fin 3,
        a x i j • directionalFDeriv (v i) (directionalFDeriv (v j) (u b)) x := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

lemma scalarFirstBase_scalarSecondBase_commutator (v : Fin 3 → R3) (a : MatrixField)
    (c : Fin 3 → R3 → ℝ) (u : R3 → SphereL2)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hc : ∀ k, ContDiff ℝ ∞ (c k)) (hu : ContDiff ℝ ∞ u) (x : R3) :
    scalarFirstBase v c (scalarSecondBase v a u) x -
      scalarSecondBase v a (scalarFirstBase v c u) x =
      scalarFirstPrincipalRemainder v a c u x := by
  have hs (X : R3) : directionalFDeriv X (scalarSecondBase v a u) =
      fun y => ∑ i, ∑ j, directionalFDeriv X
        (fun z => a z i j • directionalFDeriv (v i) (directionalFDeriv (v j) u) z) y := by
    funext y
    let F : Fin 3 → Fin 3 → R3 → SphereL2 := fun i j z =>
      a z i j • directionalFDeriv (v i) (directionalFDeriv (v j) u) z
    have hF (i j : Fin 3) : ContDiff ℝ ∞ (F i j) :=
      (ha i j).smul (contDiff_directionalFDeriv (v i) _ (contDiff_directionalFDeriv (v j) u hu))
    have hsum (i : Fin 3) : ContDiff ℝ ∞ (fun z => ∑ j : Fin 3, F i j z) :=
      ContDiff.sum (fun j _ => hF i j)
    change directionalFDeriv X (fun z => ∑ i : Fin 3, ∑ j : Fin 3, F i j z) y = _
    rw [directionalFDeriv_fintype_sum X (fun i z => ∑ j : Fin 3, F i j z) hsum y]
    apply Finset.sum_congr rfl
    intro i _
    exact directionalFDeriv_fintype_sum X (F i) (hF i) y
  have ht (X Y : R3) : directionalFDeriv X (directionalFDeriv Y (scalarFirstBase v c u)) =
      fun y => ∑ k, directionalFDeriv X (directionalFDeriv Y
        (fun z => c k z • directionalFDeriv (v k) u z)) y := by
    funext y
    exact directionalFDeriv_second_fintype_sum X Y _
      (fun k => (hc k).smul (contDiff_directionalFDeriv (v k) u hu)) y
  change (∑ k, c k x • directionalFDeriv (v k) (scalarSecondBase v a u) x) -
    (∑ i, ∑ j, a x i j • directionalFDeriv (v i)
      (directionalFDeriv (v j) (scalarFirstBase v c u)) x) = _
  simp_rw [hs, ht, Finset.smul_sum]
  have he : (∑ i, ∑ j, ∑ k, a x i j • directionalFDeriv (v i)
        (directionalFDeriv (v j) (fun z => c k z • directionalFDeriv (v k) u z)) x) =
      ∑ k, ∑ i, ∑ j, a x i j • directionalFDeriv (v i)
        (directionalFDeriv (v j) (fun z => c k z • directionalFDeriv (v k) u z)) x := by
    calc
      _ = ∑ i, ∑ k, ∑ j, a x i j • directionalFDeriv (v i)
          (directionalFDeriv (v j) (fun z => c k z • directionalFDeriv (v k) u z)) x := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  unfold scalarFirstPrincipalRemainder
  rw [he, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  exact scalar_directional_first_principal_commutator (v i) (v j) (v k)
    (fun y => a y i j) (c k) u (ha i j) (hc k) hu x

/-- The raw frame-lowering first-base operator, evaluated through its genuine
angular derivative output tuple. No degree truncation is used. -/
def contractionFirstBase (v : Fin 3 → R3) (c : Fin 3 → Fin 3 → R3 → ℝ)
    (d : Fin 3 → R3 → SphereL2) (x : R3) : SphereL2 :=
  ∑ b, scalarFirstBase v (c b) (d b) x

lemma contDiff_contractionFirstBase (v : Fin 3 → R3)
    (c : Fin 3 → Fin 3 → R3 → ℝ) (d : Fin 3 → R3 → SphereL2)
    (hc : ∀ b k, ContDiff ℝ ∞ (c b k)) (hd : ∀ b, ContDiff ℝ ∞ (d b)) :
    ContDiff ℝ ∞ (contractionFirstBase v c d) :=
  ContDiff.sum (fun b _ => contDiff_scalarFirstBase v (c b) (d b) (hc b) (hd b))

lemma contractionFirstBase_scalarSecondBase_commutator (v : Fin 3 → R3)
    (a : MatrixField) (c : Fin 3 → Fin 3 → R3 → ℝ) (d : Fin 3 → R3 → SphereL2)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hc : ∀ b k, ContDiff ℝ ∞ (c b k)) (hd : ∀ b, ContDiff ℝ ∞ (d b)) (x : R3) :
    contractionFirstBase v c (fun b => scalarSecondBase v a (d b)) x -
      scalarSecondBase v a (contractionFirstBase v c d) x =
      ∑ b, scalarFirstPrincipalRemainder v a (c b) (d b) x := by
  unfold contractionFirstBase
  rw [scalarSecondBase_fintype_sum v a _
    (fun b => contDiff_scalarFirstBase v (c b) (d b) (hc b) (hd b)) x,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  exact scalarFirstBase_scalarSecondBase_commutator v a (c b) (d b) ha (hc b) (hd b) x

/-- Every scalar principal image remains in the exact maximal A_b graph,
including the native degree-zero output. -/
lemma scalarSecondBase_sphereDerivativeGraph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (b : Fin 3)
    (v : Fin 3 → R3) (a : MatrixField) (u d : R3 → SphereL2)
    (hu : ContDiff ℝ ∞ u) (hd : ContDiff ℝ ∞ d)
    (hgraph : ∀ x, (u x,d x) ∈ sphereDerivativeGraph hF hO hD b) (x : R3) :
    (scalarSecondBase v a u x,scalarSecondBase v a d x) ∈ sphereDerivativeGraph hF hO hD b := by
  have hsecond (i j : Fin 3) (y : R3) :
      (directionalFDeriv (v i) (directionalFDeriv (v j) u) y,
       directionalFDeriv (v i) (directionalFDeriv (v j) d) y) ∈
        sphereDerivativeGraph hF hO hD b := by
    apply directional_sphereDerivativeGraph hF hO hD b (v i)
      (directionalFDeriv (v j) u) (directionalFDeriv (v j) d)
      (contDiff_directionalFDeriv (v j) u hu) (contDiff_directionalFDeriv (v j) d hd)
    intro z
    exact directional_sphereDerivativeGraph hF hO hD b (v j) u d hu hd hgraph z
  intro m
  simp only [scalarSecondBase,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hsecond i j x m]

lemma scalarSecondBase_directional_sphereDerivativeGraph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (b : Fin 3)
    (v : Fin 3 → R3) (a : MatrixField) (u d : R3 → SphereL2)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hu : ContDiff ℝ ∞ u) (hd : ContDiff ℝ ∞ d)
    (hgraph : ∀ x, (u x,d x) ∈ sphereDerivativeGraph hF hO hD b) (X x : R3) :
    (directionalFDeriv X (scalarSecondBase v a u) x,
     directionalFDeriv X (scalarSecondBase v a d) x) ∈ sphereDerivativeGraph hF hO hD b :=
  directional_sphereDerivativeGraph hF hO hD b X _ _
    (contDiff_scalarSecondBase v a u ha hu) (contDiff_scalarSecondBase v a d ha hd)
    (scalarSecondBase_sphereDerivativeGraph hF hO hD b v a u d hu hd hgraph) x

lemma contractionFirstBase_graph_output_independent (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (v : Fin 3 → R3) (c : Fin 3 → Fin 3 → R3 → ℝ) (u : R3 → SphereL2)
    (d d' : Fin 3 → R3 → SphereL2)
    (hd : ∀ b x, (u x,d b x) ∈ sphereDerivativeGraph hF hO hD b)
    (hd' : ∀ b x, (u x,d' b x) ∈ sphereDerivativeGraph hF hO hD b) :
    contractionFirstBase v c d = contractionFirstBase v c d' := by
  have he : d = d' := by
    funext b x
    exact sphereDerivativeGraph_output_unique hF hO hD b (u x) (d b x) (d' b x) (hd b x) (hd' b x)
  rw [he]

def negativeFrameEntry (g : MatrixField) (L lam : ℝ) (b k : Fin 3) (x : R3) : ℝ :=
  -frameEntry g L b k (lam,x)

lemma contDiff_negativeFrameEntry (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (b k : Fin 3) : ContDiff ℝ ∞ (negativeFrameEntry g L lam b k) :=
  ((contDiff_frameEntry g hg L b k).comp (contDiff_const.prodMk contDiff_id)).neg

lemma directional_negativeFrameEntry (g : MatrixField) (L lam : ℝ)
    (b k q : Fin 3) (x : R3) :
    directionalFDeriv (coordinateDirection q) (negativeFrameEntry g L lam b k) x =
      -familyDirectionalDeriv q (frameEntry g L b k) (lam,x) := by
  change fderiv ℝ (fun y : R3 => -frameEntry g L b k (lam,y)) x
    (coordinateDirection q) = -familyDirectionalDeriv q (frameEntry g L b k) (lam,x)
  rw [fderiv_fun_neg (𝕜 := ℝ) (x := x)
    (f := fun y : R3 => frameEntry g L b k (lam,y))]
  rfl

lemma second_directional_negativeFrameEntry (g : MatrixField) (L lam : ℝ)
    (b k i j : Fin 3) (x : R3) :
    directionalFDeriv (coordinateDirection i)
      (directionalFDeriv (coordinateDirection j) (negativeFrameEntry g L lam b k)) x =
      -familyDirectionalDeriv i (familyDirectionalDeriv j (frameEntry g L b k)) (lam,x) := by
  rw [show directionalFDeriv (coordinateDirection j) (negativeFrameEntry g L lam b k) =
    fun y => -familyDirectionalDeriv j (frameEntry g L b k) (lam,y) from
      funext (directional_negativeFrameEntry g L lam b k j)]
  simp only [familyDirectionalDeriv,directionalFDeriv,fderiv_fun_neg,ContinuousLinearMap.neg_apply]

/-- This is Σ_k -Σ_b e_bk A_b ∂_k φ, through graph outputs on the actual
smooth ambient core. It is not a continuous operator on all SphereL2. -/
def actualFrameFirstBase (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (L lam : ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  contractionFirstBase coordinateDirection (negativeFrameEntry g L lam)
    (fun b => ambientDerivativeField hF hO hD b G hG)

/-- Raw lower-first applied to the actual scalar principal image. The graph
certificate below supplies the complete unbounded domain of this composition. -/
def actualFrameFirstPrincipalComposition (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  contractionFirstBase coordinateDirection (negativeFrameEntry g L lam)
    (fun b => scalarSecondBase coordinateDirection
      (actualPrincipalMatrix g L lam δ R p h) (ambientDerivativeField hF hO hD b G hG))

def actualFrameFirstPrincipalCommutator (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  actualFrameFirstPrincipalComposition hF hO hD g L lam δ R p h G hG x -
    scalarSecondBase coordinateDirection (actualPrincipalMatrix g L lam δ R p h)
      (actualFrameFirstBase hF hO hD g L lam G hG) x

def actualFrameFirstPrincipalRemainder (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  ∑ k, ∑ i, ∑ j,
    (directionalFDeriv (coordinateDirection k)
       (fun y => actualPrincipalMatrix g L lam δ R p h y i j) x •
       (-(∑ b, frameEntry g L b k (lam,x) •
         directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j)
           (ambientDerivativeField hF hO hD b G hG)) x)) -
     actualPrincipalMatrix g L lam δ R p h x i j •
       (-(∑ b, familyDirectionalDeriv i (familyDirectionalDeriv j (frameEntry g L b k)) (lam,x) •
         directionalFDeriv (coordinateDirection k) (ambientDerivativeField hF hO hD b G hG) x)) -
     actualPrincipalMatrix g L lam δ R p h x i j •
       (-(∑ b, familyDirectionalDeriv j (frameEntry g L b k) (lam,x) •
         directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection k)
           (ambientDerivativeField hF hO hD b G hG)) x)) -
     actualPrincipalMatrix g L lam δ R p h x i j •
       (-(∑ b, familyDirectionalDeriv i (frameEntry g L b k) (lam,x) •
         directionalFDeriv (coordinateDirection j) (directionalFDeriv (coordinateDirection k)
           (ambientDerivativeField hF hO hD b G hG)) x)))

/-- No spectral cutoff: every base derivative of the scalar principal field
has the genuine A_b graph output used in the first raw composition. -/
theorem actualFrameFirstPrincipalComposition_graph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hδ : 0 < δ) (hR : 0 < R)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (b k : Fin 3) (x : R3) :
    (directionalFDeriv (coordinateDirection k) (scalarSecondBase coordinateDirection
       (actualPrincipalMatrix g L lam δ R p h) (ambientSphereL2 G hG)) x,
     directionalFDeriv (coordinateDirection k) (scalarSecondBase coordinateDirection
       (actualPrincipalMatrix g L lam δ R p h) (ambientDerivativeField hF hO hD b G hG)) x) ∈
      sphereDerivativeGraph hF hO hD b :=
  scalarSecondBase_directional_sphereDerivativeGraph hF hO hD b coordinateDirection
    (actualPrincipalMatrix g L lam δ R p h) (ambientSphereL2 G hG)
    (ambientDerivativeField hF hO hD b G hG)
    (OAI.AnisotropicCalderon.ActualPerturbedDefect.contDiff_actualPrincipalMatrix_entry g hg L lam δ R p h hδ hR hh)
    (contDiff_ambientSphereL2 G hG) (contDiff_ambientDerivativeField hF hO hD b G hG)
    (ambientDerivativeField_graph hF hO hD b G hG) (coordinateDirection k) x

lemma sum_four_reorder (F : Fin 3 → Fin 3 → Fin 3 → Fin 3 → SphereL2) :
    (∑ b, ∑ k, ∑ i, ∑ j, F b k i j) = ∑ k, ∑ i, ∑ j, ∑ b, F b k i j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm

/-- Actual all-degree smooth-core first-principal identity. Only the output
fields of the exact unbounded angular graph are differentiated in the base. -/
theorem actualFrameFirstPrincipal_commutator_normal_form (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hδ : 0 < δ) (hR : 0 < R)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    actualFrameFirstPrincipalCommutator hF hO hD g L lam δ R p h G hG x =
      actualFrameFirstPrincipalRemainder hF hO hD g L lam δ R p h G hG x := by
  unfold actualFrameFirstPrincipalCommutator actualFrameFirstPrincipalComposition actualFrameFirstBase
  rw [contractionFirstBase_scalarSecondBase_commutator coordinateDirection
    (actualPrincipalMatrix g L lam δ R p h) (negativeFrameEntry g L lam)
    (fun b => ambientDerivativeField hF hO hD b G hG)
    (OAI.AnisotropicCalderon.ActualPerturbedDefect.contDiff_actualPrincipalMatrix_entry g hg L lam δ R p h hδ hR hh)
    (contDiff_negativeFrameEntry g hg L lam)
    (fun b => contDiff_ambientDerivativeField hF hO hD b G hG) x]
  unfold scalarFirstPrincipalRemainder actualFrameFirstPrincipalRemainder
  rw [sum_four_reorder]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [directional_negativeFrameEntry,second_directional_negativeFrameEntry]
  simp only [negativeFrameEntry,neg_smul,← Finset.sum_neg_distrib,Finset.sum_sub_distrib,
    Finset.smul_sum,smul_neg]

/-- Literal source correspondence for the four terms, including both ordered
mixed frame derivatives and the double negative signs. -/
theorem actualFrameFirstPrincipal_commutator_pair (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hδ : 0 < δ) (hR : 0 < R)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    ⟪actualFrameFirstPrincipalCommutator hF hO hD g L lam δ R p h G hG x,
      ambientSphereL2 G hG x⟫_ℝ =
      ∑ t : Fin 3 × Fin 3 × Fin 3,
        (firstPrincipalContribution hF hO hD g L lam δ R p h t.1 t.2.1 t.2.2 G hG x +
         secondFrameContribution hF hO hD g L lam δ R p h t.1 t.2.1 t.2.2 G hG x +
         firstFrameContribution hF hO hD g L lam δ R p h t.1 t.2.2 t.2.1 t.2.2 t.2.1 t.1 G hG x +
         firstFrameContribution hF hO hD g L lam δ R p h t.1 t.2.1 t.2.1 t.2.2 t.2.2 t.1 G hG x) := by
  rw [actualFrameFirstPrincipal_commutator_normal_form hF hO hD g hg L lam δ R p h hδ hR hh G hG x]
  simp only [actualFrameFirstPrincipalRemainder,Fintype.sum_prod_type,sum_inner,
    inner_sub_left,firstPrincipalContribution,secondFrameContribution,firstFrameContribution,
    inner_neg_left,neg_smul,smul_neg]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  abel

end OAI.AnisotropicCalderon.ActualUnboundedFirstPrincipalNormalForm
