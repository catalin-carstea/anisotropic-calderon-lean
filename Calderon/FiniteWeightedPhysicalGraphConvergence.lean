import Calderon.SupportedWeightedSphereL2Graph
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic ReferenceDensityBounds WeightedBaseSpectral
attribute [local irreducible] harmonicSphereSubspace

theorem referenceBaseLift_finite_sum
    (g:MatrixField) (hg:IsAdmissibleMetric g) (L q:ℝ)
    {ι:Type*} (s:Finset ι) (u:ι→R3→SphereL2)
    (hu:∀ i,Continuous (u i)) (hc:∀ i,HasCompactSupport (u i)):
    referenceBaseLift g hg L q (fun y => ∑ i∈s,u i y)
      (continuous_finsetSum _ (fun i _ => hu i)) (show HasCompactSupport (fun y => ∑ i∈s,u i y) from by
        convert (HasCompactSupport.finset_sum (s:=s) (f:=u) (fun i _ => hc i)) using 1
        funext y
        simp only [Finset.sum_apply])=
      ∑ i∈s,referenceBaseLift g hg L q (u i) (hu i) (hc i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact MemLp.toLp_zero _
  | @insert i s hi ih =>
      have hS:Continuous (fun y => ∑ j∈s,u j y) := continuous_finsetSum _ (fun j _ => hu j)
      have hSc:HasCompactSupport (fun y => ∑ j∈s,u j y) := by
        convert (HasCompactSupport.finset_sum (s:=s) (f:=u) (fun j _ => hc j)) using 1
        funext y
        simp only [Finset.sum_apply]
      have hAdd:referenceBaseLift g hg L q (fun y => u i y+∑ j∈s,u j y) ((hu i).add hS) ((hc i).add hSc)=
          referenceBaseLift g hg L q (u i) (hu i) (hc i)+
            referenceBaseLift g hg L q (fun y => ∑ j∈s,u j y) hS hSc :=
        MemLp.toLp_add (memLp_referenceBase g hg L q (u i) (hu i) (hc i))
          (memLp_referenceBase g hg L q (fun y => ∑ j∈s,u j y) hS hSc)
      simpa only [Finset.sum_insert hi,ih] using hAdd

theorem tendsto_weighted_square_error_finite_sum
    (g:MatrixField) (hg:IsAdmissibleMetric g) (L q:ℝ)
    {ι:Type*} (s:Finset ι) (U:ι→ℕ→R3→SphereL2) (u:ι→R3→SphereL2)
    (hU:∀ i n,Continuous (U i n)) (hu:∀ i,Continuous (u i))
    (hUc:∀ i n,HasCompactSupport (U i n)) (huc:∀ i,HasCompactSupport (u i))
    (hLimit:∀ i,Tendsto (fun n:ℕ => ∫ y,referenceDensityFamily g L (q,y)*‖U i n y-u i y‖^2) atTop (𝓝 0)):
    Tendsto (fun n:ℕ => ∫ y,referenceDensityFamily g L (q,y)*‖(∑ i∈s,U i n y)-(∑ i∈s,u i y)‖^2)
      atTop (𝓝 0) := by
  have hEach (i:ι):=tendsto_referenceBaseLift_of_weighted_sq_tendsto g hg L q (U i) (u i)
    (hU i) (hu i) (hUc i) (huc i) (hLimit i)
  have hSum:=tendsto_finsetSum s (fun i _ => hEach i)
  have hNorm:=((tendsto_iff_dist_tendsto_zero.mp hSum).pow 2)
  have hConv (n:ℕ):‖(∑ i∈s,referenceBaseLift g hg L q (U i n) (hU i n) (hUc i n))-
      (∑ i∈s,referenceBaseLift g hg L q (u i) (hu i) (huc i))‖^2=
      ∫ y,referenceDensityFamily g L (q,y)*‖(∑ i∈s,U i n y)-(∑ i∈s,u i y)‖^2 := by
    rw [←referenceBaseLift_finite_sum,←referenceBaseLift_finite_sum,←referenceBaseLift_sub]
    exact norm_sq_referenceBaseLift g hg L q _ _ _
  simpa only [dist_eq_norm,hConv,zero_pow (by norm_num:2≠0)] using hNorm

end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
