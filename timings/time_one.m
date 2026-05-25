// Time one (h, D, algorithm) triple. CLI args via `magma -b`:
//   c     := <coefficient list, parsed via eval>
//   D     := <integer>
//   alg   := "IsogenyGraphBuilder" | "IsogenyOrbitBuilder" | "Polarization"
//   label := "<label string>"
//   abvarfq_spec := "<path to AbVarFq spec>"
//
// Output: one TSV row to stdout:
//   label \t D \t alg \t walltime_seconds \t peak_memory_mb \t status
// where status in {ok, error}. timeout / oom rows are written by run_all.sh
// from exit-code detection — this script does not emit them itself.
//
// IMPORTANT: To equalize the AlgEtQOrd cache state across all three branches,
// every branch builds If/R/PHI BEFORE the timer starts. The graph and orbit
// branches then ignore PHI; only Polarization uses it. Without this, the
// polarization cell would warm Picard-related caches via pAdicPosCMType
// that the graph/orbit cells did not, contaminating cross-cell comparisons.
//
// Magma quirk: `magma -b foo:=bar` binds `foo` to the *string* "bar",
// regardless of bar's intended type. So every CLI arg — even numeric D
// and even bare-string args — must be passed through eval() to recover
// the Magma value. For `c` (a coefficient list whose source form was
// already double-quoted in the shell as 'c:="[ 4, -3, 1 ]"') we eval
// twice: the first strips the outer quotes to recover the inner
// expression "[ 4, -3, 1 ]", the second parses that as a Magma sequence.

SetColumns(0);
SetClassGroupBounds("GRH");

abvarfq_spec_path := eval(abvarfq_spec);
alg_name := eval(alg);
label_str := eval(label);
D_int := eval(D);

AttachSpec(abvarfq_spec_path);     // AbVarFq first (external dep)
AttachSpec("../spec");             // AbVarFqIsogenies (package-local)

PP<x> := PolynomialRing(Integers());
h := PP!eval(eval(c));              // `c` arrives as a quoted string; eval twice.

If := IsogenyClass(h:Check:=false);
R := ZFVOrder(If);
PHI := pAdicPosCMType(If);          // pre-computed in every branch

status := "ok";
t0 := Realtime();
try
    case alg_name:
        when "IsogenyGraphBuilder":
            _ := IsogenyGraphBuilder(R, D_int);
        when "IsogenyOrbitBuilder":
            _ := IsogenyOrbitBuilder(R, D_int);
        when "Polarization":
            _ := NonPrincipalPolarizationsOfDegreeDividing(R, PHI, D_int);
        else:
            error "unknown alg: " cat alg_name;
    end case;
catch e
    status := "error";
end try;
elapsed := Realtime(t0);
mem_mb := GetMaximumMemoryUsage() / (1024.0 * 1024.0);

printf "%o\t%o\t%o\t%o\t%o\t%o\n",
       label_str, D_int, alg_name, elapsed, mem_mb, status;
quit;
