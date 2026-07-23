# Succinct proof

Let \(D=\operatorname{diam}(G)\), let
\(\bar e=\overline{\operatorname{ecc}}(G)\), and choose a diametral geodesic
\(P=v_0v_1\cdots v_D\). Since \(P\) is induced and bipartite, while every
eccentricity is at most \(D\),

\[
D+1\le b(G)\le2+\bar e\le D+2.
\]

Thus \(b(G)\) is either \(D+1\) or \(D+2\).

## Case \(b(G)=D+1\)

For \(x\notin P\), the induced graph on \(P\cup\{x\}\) has \(D+2\)
vertices and is not bipartite. Hence \(x\) has neighbors on \(P\) of both
parities. Any two such neighbors have indices differing by at most two;
otherwise the two-edge detour through \(x\) shortens \(P\). If \(j\) is the
least neighbor index, then

\[
N(x)\cap V(P)=\{v_j,v_{j+1}\}
\quad\text{or}\quad
\{v_j,v_{j+1},v_{j+2}\}.
\]

Let \(X_j\) be the outside vertices with least neighbor index \(j\). Each
\(X_j\) is a clique: if nonadjacent \(x,y\in X_j\) existed, deleting
\(v_{j+1}\) from \(P\) and adding \(x,y\) would give an induced bipartite
subgraph on \(D+2\) vertices. Therefore

\[
v_0,\ X_0,\ v_1,\ X_1,\ldots,v_{D-1},\ X_{D-1},\ v_D
\]

is a Hamiltonian path, with each nonempty \(X_j\) traversed in any order.

## Case \(b(G)=D+2\)

Equality in the displayed chain gives \(\bar e=D\). Since every eccentricity
is at most \(D\), all vertices have eccentricity \(D\), so
\(\operatorname{rad}(G)=D\). The classical inequality
\(b(G)\ge2\operatorname{rad}(G)\) now gives

\[
2D\le D+2,
\]

and hence \(D\le2\). Diameter one is impossible in this equality case because
a nontrivial complete graph has bipartite number two. Thus \(D=2\) and
\(b(G)=4\).

The graph has no cut vertex. If \(c\) were one, then for any \(w\ne c\),
choosing \(y\) in another component of \(G-c\) shows that a length-at-most-two
\(w\)-\(y\) path must be \(wcy\). Hence every vertex other than \(c\) is
adjacent to \(c\), contradicting \(\operatorname{ecc}(c)=2\). The graph is
therefore 2-connected. Finally, a maximum independent set \(I\), together
with any vertex outside it, induces a bipartite graph. Thus
\(\alpha(G)+1\le b(G)=4\), so \(\alpha(G)\le3\). The
Chvátal--Erdős path theorem yields a Hamiltonian path.
