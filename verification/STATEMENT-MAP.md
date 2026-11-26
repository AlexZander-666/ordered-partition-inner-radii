# Statement correspondence

Original object: ordered lists of disjoint nonempty blocks partitioning a labelled n-set, with one marker for every block of size at least j. The module OriginalEGF links the ordered row to the exponential generating function. The formal offset k represents j−2.

- Theorem 1, compact-uniform limit. CriticalEdge.original_inner_sinc_limit, for every integer k ≥ 2 and every bounded closed complex disk centered at zero. The parameter is t = 1−C−Lu/n². normalizedInnerRow uses a^n·a(j−1)/n divided by n!, since a²Dzz/2 = a(j−1). The limiting series is innerSinc.
- Theorem 1, both limits. CriticalEdge.original_inner_radii uses infDist at 1 and 0 to the full complex set of zeros of the same row. This set is finite because the row is nonzero (for example its evaluation at 1 counts all ordered partitions), and eventual_real_witness gives eventual nonemptiness. Thus both infima are minima eventually. The critical point is unique by strict_maximum.
- Theorem 1, finite lower bounds. CriticalEdge.root_distance_log_bound applies to every complex zero and all n ≥ 3. The parameter height identity is discharged in original_log_radius and again in original_inner_radii. Its radialLoss equals H log(n)/n.
- Scaling and contact. CriticalEdge.critical_contact, critical_ratio and critical_curvature give the positive double root and explicit scale. Original row zeros include both real and nonreal roots without distinction. The paper uses the sign change of the limiting sinc across π² to bound the two upper deviations. eventual_real_witness uses the same sign argument.
