import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.ContinuousMap.Basic

/-! EXPANSION.json precedes this independent standard gluing argument.
Actual physical local representatives remain to be derived from the existing native source solver. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped Topology
namespace OAI.AnisotropicCalderon.ContinuousRepresentative

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [SecondCountableTopology X]

theorem exists_continuousOn_representative_of_locally_ae
    (μ : Measure X) [Measure.IsOpenPosMeasure μ]
    (U : Set X) (hU : IsOpen U) (k : X → ℝ)
    (hLocal : ∀ x ∈ U, ∃ V : Set X,
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∃ f : X → ℝ,
        ContinuousOn f V ∧ f =ᵐ[μ.restrict V] k) :
    ∃ F : X → ℝ, ContinuousOn F U ∧ F =ᵐ[μ.restrict U] k := by
  classical
  have hLocal' (i : U) : ∃ V : Set X,
      IsOpen V ∧ (i : X) ∈ V ∧ V ⊆ U ∧ ∃ f : X → ℝ,
        ContinuousOn f V ∧ f =ᵐ[μ.restrict V] k := hLocal i i.property
  choose V hVo hiV hVU f hfc hfa using hLocal'
  have hCompat (i j : U) : EqOn (f i) (f j) (V i ∩ V j) := by
    have hi : f i =ᵐ[μ.restrict (V i ∩ V j)] k :=
      (hfa i).filter_mono (ae_mono (Measure.restrict_mono_set μ inter_subset_left))
    have hj : f j =ᵐ[μ.restrict (V i ∩ V j)] k :=
      (hfa j).filter_mono (ae_mono (Measure.restrict_mono_set μ inter_subset_right))
    exact Measure.eqOn_open_of_ae_eq (μ := μ) (hi.trans hj.symm)
      ((hVo i).inter (hVo j)) ((hfc i).mono inter_subset_left)
      ((hfc j).mono inter_subset_right)
  let S (i : U) : Set U := {y | (y : X) ∈ V i}
  let φ (i : U) : C(S i, ℝ) :=
    ⟨(fun y => f i (y.1 : X)), by
      have hc : Continuous (fun y : S i => (y.1 : X)) :=
        continuous_subtype_val.comp continuous_subtype_val
      exact (hfc i).comp_continuous hc (fun y => y.property)⟩
  have hφ (i j : U) (x : U) (hxi : x ∈ S i) (hxj : x ∈ S j) :
      φ i ⟨x,hxi⟩ = φ j ⟨x,hxj⟩ := by
    change f i (x : X) = f j (x : X)
    exact hCompat i j ⟨hxi,hxj⟩
  have hS (x : U) : ∃ i : U, S i ∈ 𝓝 x := by
    refine ⟨x,?_⟩
    exact ((hVo x).preimage continuous_subtype_val).mem_nhds (hiV x)
  let G : C(U, ℝ) := ContinuousMap.liftCover S φ hφ hS
  let F : X → ℝ := fun x => if hx : x ∈ U then G ⟨x,hx⟩ else 0
  have hF (x : X) (hx : x ∈ U) : F x = G ⟨x,hx⟩ := by
    dsimp only [F]
    rw [dif_pos hx]
  have hCont : ContinuousOn F U := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun x : U => F x)
    have hEq : (fun x : U => F x) = (G : U → ℝ) := by
      funext x
      exact hF x x.property
    rw [hEq]
    exact G.continuous
  have hEqLocal (i : U) : EqOn F (f i) (V i) := by
    intro x hx
    have hxU : x ∈ U := hVU i hx
    calc
      F x = G ⟨x,hxU⟩ := hF x hxU
      _ = f i x := by
        exact ContinuousMap.liftCover_coe (S := S) (φ := φ) (hφ := hφ) (hS := hS)
          (i := i) (⟨⟨x,hxU⟩,hx⟩ : S i)
  have hAEi (i : U) : F =ᵐ[μ.restrict (V i)] k :=
    ((hEqLocal i).aeEq_restrict (hVo i).measurableSet).trans (hfa i)
  have hCover : U ⊆ ⋃ i : U, V i := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,hiV ⟨x,hx⟩⟩
  obtain ⟨r,hr,hrCover⟩ :=
    (HereditarilyLindelofSpace.isLindelof U).elim_countable_subcover V hVo hCover
  have hUnion : (⋃ i ∈ r, V i) = U :=
    subset_antisymm (iUnion₂_subset (fun i _ => hVU i)) hrCover
  have hAE : F =ᵐ[μ.restrict (⋃ i ∈ r, V i)] k :=
    (ae_eq_restrict_biUnion_iff V hr F k).mpr (fun i _ => hAEi i)
  rw [hUnion] at hAE
  exact ⟨F,hCont,hAE⟩

theorem eqOn_of_continuousOn_representatives_ae
    (μ : Measure X) [Measure.IsOpenPosMeasure μ]
    (U : Set X) (hU : IsOpen U) (k F G : X → ℝ)
    (hF : ContinuousOn F U) (hG : ContinuousOn G U)
    (hFA : F =ᵐ[μ.restrict U] k) (hGA : G =ᵐ[μ.restrict U] k) :
    EqOn F G U :=
  Measure.eqOn_open_of_ae_eq (μ := μ) (hFA.trans hGA.symm) hU hF hG

end OAI.AnisotropicCalderon.ContinuousRepresentative
