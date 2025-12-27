// Équivalent Dafny de triselection_comparison.mlw
// 
// INSTALLATION DAFNY REQUISE:
// - Dafny 4.x+ requis (version Ubuntu 2.3.0 trop ancienne)
// - Télécharger depuis: https://github.com/dafny-lang/dafny/releases/latest
// 
// VÉRIFICATION:
//   dafny verify --log-format text SelectionSort.dfy
// EXÉCUTION:
//   dafny run SelectionSort.dfy
//
// NOTE: Ce fichier démontre la traduction directe Why3 → Dafny
// avec comparaison FOR (fermé [k+1, n-1]) vs WHILE (semi-ouvert [k+1, n))

// ============================================================================
// PREDICATS AUXILIAIRES (équivalents aux use Array.*)
// ============================================================================

predicate sorted(a: array<int>, lo: int, hi: int)
  reads a
  requires 0 <= lo <= hi <= a.Length
{
  forall i, j :: lo <= i < j < hi ==> a[i] <= a[j]
}

predicate partitioned(a: array<int>, pivot: int)
  reads a
  requires 0 <= pivot <= a.Length
{
  forall i, j :: 0 <= i < pivot <= j < a.Length ==> a[i] <= a[j]
}

// ============================================================================
// VERSION ORIGINALE avec FOR (intervalle fermé [k+1, n-1])
// ============================================================================

method argmin_for(a: array<int>, k: int) returns (imin: int)
  requires a.Length > 0
  requires 0 <= k < a.Length
  ensures k <= imin < a.Length
  ensures forall i :: k <= i < a.Length ==> a[imin] <= a[i]
{
  var n := a.Length;
  imin := k;
  
  // FOR i = k+1 TO n-1 (intervalle fermé [k+1, n-1])
  var i := k + 1;
  while i <= n - 1
    invariant k + 1 <= i <= n
    invariant k <= imin < i
    invariant forall j :: k <= j < i ==> a[imin] <= a[j]
    decreases n - i
  {
    if a[i] < a[imin] {
      imin := i;
    }
    i := i + 1;
  }
}

// ============================================================================
// VERSION WHILE avec intervalle semi-ouvert [k+1, n)
// ============================================================================

method argmin_while(a: array<int>, k: int) returns (imin: int)
  requires a.Length > 0
  requires 0 <= k < a.Length
  ensures k <= imin < a.Length
  ensures forall i :: k <= i < a.Length ==> a[imin] <= a[i]
{
  var n := a.Length;
  imin := k;
  
  // WHILE i < n (intervalle semi-ouvert [k+1, n))
  var i := k + 1;
  while i < n
    invariant k + 1 <= i <= n
    invariant k <= imin < i
    invariant forall j :: k <= j < i ==> a[imin] <= a[j]
    decreases n - i
  {
    if a[i] < a[imin] {
      imin := i;
    }
    i := i + 1;
  }
}

// ============================================================================
// VERSION ORIGINALE avec FOR (intervalle fermé [0, n-1])
// ============================================================================

method SelectionSort_For(a: array<int>)
  modifies a
  ensures sorted(a, 0, a.Length)
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  var n := a.Length;
  
  // FOR i = 0 TO n-1 (intervalle fermé [0, n-1])
  var i := 0;
  while i <= n - 1
    invariant 0 <= i <= n
    invariant sorted(a, 0, i)
    invariant partitioned(a, i)
    invariant multiset(a[..]) == multiset(old(a[..]))
    decreases n - i
  {
    var imin := argmin_for(a, i);
    
    // Swap a[i] and a[imin]
    var tmp := a[imin];
    a[imin] := a[i];
    a[i] := tmp;
    
    i := i + 1;
  }
}

// ============================================================================
// VERSION WHILE avec intervalle semi-ouvert [0, n)
// ============================================================================

method SelectionSort_While(a: array<int>)
  modifies a
  ensures sorted(a, 0, a.Length)
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  var n := a.Length;
  
  // WHILE i < n (intervalle semi-ouvert [0, n))
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant sorted(a, 0, i)
    invariant partitioned(a, i)
    invariant multiset(a[..]) == multiset(old(a[..]))
    decreases n - i
  {
    var imin := argmin_while(a, i);
    
    // Swap a[i] and a[imin]
    var tmp := a[imin];
    a[imin] := a[i];
    a[i] := tmp;
    
    i := i + 1;
  }
}

// ============================================================================
// TESTS
// ============================================================================

method Main()
{
  var a1 := new int[5] [3, 1, 4, 1, 5];
  SelectionSort_For(a1);
  print "FOR version: ", a1[..], "\n";
  
  var a2 := new int[5] [3, 1, 4, 1, 5];
  SelectionSort_While(a2);
  print "WHILE version: ", a2[..], "\n";
}
