# pragma GCC optimize("Ofast, no-stack-protector, unroll-loops")
# include<bits/stdc++.h>
# define rep(i,a,b) for(int i=(a); i<=(b); i++)
# define per(i,a,b) for(int i=(a); i>=(b); i--)

int n, m, a[maxn];
vector<int> tmp[maxn], e[maxn];

int dfn, in[maxn], fa[maxn], son[maxn], sz[maxn], dep[maxn], top[maxn], id[maxn];
void dfs(int u, int p) {
    sz[u] = 1;
    fa[u] = p;
    dep[u] = dep[p] + 1;
    for (auto v : e[u]) if (v != p) {
        dfs(v, u);
        sz[u] += sz[v];
        if (!son[u] || sz[son[u]] < sz[v]) son[u] = v;
    }
}

void DFS(int u, int p) {
    top[u] = p;
    in[u] = ++dfn;
    id[dfn] = u;
    if (son[u]) DFS(son[u], p);
    for (auto v : e[u])
        if (v != fa[u] && v != son[u])
            DFS(v, v);
}
int lca(int u, int v) {
    while (top[u] != top[v]) {
        if (dep[top[u]] < dep[top[v]]) swap(u, v);
        u = fa[top[u]];
    }
    return u < v ? u : v;
}
struct Info {
    int pre, suf, Max, len;
    Info() { pre = suf = Max = len = 0; }
    Info(int _pre, int _suf, int _Max, int _len) : pre(_pre), suf(_suf), Max(_Max), len(_len) {}
};
Info operator+(const Info &x, const Info &y) {
    Info res;
    res.pre = (x.pre == x.len ? x.pre + y.pre : x.pre);
    res.suf = (y.suf == y.len ? x.suf + y.suf : y.suf);
    res.Max = max({x.Max, y.Max, x.suf + y.pre});
    res.len = x.len + y.len;
    return res;
}
Info sum[maxn << 5];
int ls[maxn << 5], rs[maxn << 5], root[maxn << 5], idx;

void clear() {
    for (int i = 0; i <= n + 1; ++i) {
        son[i] = 0;
        root[i] = 0;
        e[i].clear();
        tmp[i].clear();
    }
    for (int i = 0; i <= idx; ++i) {
        sum[i] = Info();
        ls[i] = rs[i] = 0;
    }
    idx = dfn = 0;
}
void build(int &rt, int l, int r) {
    rt = ++idx;
    sum[rt] = Info(0, 0, 0, r - l + 1);
    if (l == r) return ;
    int mid = l + r >> 1;
    build(ls[rt], l, mid); build(rs[rt], mid + 1, r);
}

void insert(int rtu, int &rtv, int l, int r, int pos) {
    rtv = ++idx;
    ls[rtv] = ls[rtu], rs[rtv] = rs[rtu], sum[rtv] = sum[rtu];
    if (l == r) {
        sum[rtv] = Info(1, 1, 1, 1);
        return ;
    }
    int mid = l + r >> 1;
    if (pos <= mid) insert(ls[rtu], ls[rtv], l, mid, pos);
    else insert(rs[rtu], rs[rtv], mid + 1, r, pos);
    sum[rtv] = sum[ls[rtv]] + sum[rs[rtv]];
}


void linkCopy(int &rtu, int rtv, int l, int r, int ql, int qr) {
    int p = rtu;
    rtu = ++idx;
    sum[rtu] = sum[p], ls[rtu] = ls[p], rs[rtu] = rs[p];
    if (ql <= l && r <= qr) {
        sum[rtu] = sum[rtv];
        ls[rtu] = ls[rtv];
        rs[rtu] = rs[rtv];
        return ;
    }
    int mid = l + r >> 1;
    if (ql <= mid) linkCopy(ls[rtu], ls[rtv], l, mid, ql, qr);
    if (mid < qr) linkCopy(rs[rtu], rs[rtv], mid + 1, r, ql, qr);
    sum[rtu] = sum[ls[rtu]] + sum[rs[rtu]];
}

void Copy(int u, int v, int rtu, int rtv) {
    while (top[u] != top[v]) {
        if (dep[top[u]] < dep[top[v]]) swap(u, v);
        linkCopy(root[rtu], root[rtv], 1, n, in[top[u]], in[u]);
        u = fa[top[u]];
    }
    if (dep[u] > dep[v]) swap(u, v);
    linkCopy(root[rtu], root[rtv], 1, n, in[u], in[v]);
}

Info linkQuery(int rt, int l, int r, int ql, int qr) {
    if (ql <= l && r <= qr) return sum[rt];
    int mid = l + r >> 1;
    Info Ans;
    if (ql <= mid) Ans = Ans + linkQuery(ls[rt], l, mid, ql, qr);
    if (mid < qr) Ans = Ans + linkQuery(rs[rt], mid + 1, r, ql, qr);
    return Ans;
}


void Query(int u, int v, int rt, int l) {
    int U = u;
    vector<pii> link, revlink;
    while(top[u] != top[v]) {
        if (dep[top[u]] > dep[top[v]]) {
            link.emplace_back(in[u], in[top[u]]);
            u = fa[top[u]];
        } else {
            revlink.emplace_back(in[top[v]], in[v]);
            v = fa[top[v]];
        }
    }
    link.pb(mkp(in[u], in[v]));
    for (int i = SZ(revlink) - 1; i >= 0; --i) link.emplace_back(revlink[i]);
    Info Ans;
    int pos = 0;
    vector<pii> preSeg;
    for (auto i : link) {
        auto [x, y] = i;
        Info now = x < y ? linkQuery(root[rt], 1, n, x, y) : linkQuery(root[rt], 1, n, y, x);
        if (x > y) swap(now.pre, now.suf);
         if (Ans.suf + now.pre >= l && Ans.suf) {
            for (int j = SZ(preSeg) - 1; j >= 0; --j) {
                int len = abs(preSeg[j].fir - preSeg[j].sec) + 1;
                if (Ans.suf > len) Ans.suf -= len;
                else {
                    auto [X, Y] = preSeg[j];
                    if (X < Y) pos = id[Y - Ans.suf + 1];
                    else pos = id[Y + Ans.suf - 1];
                    break;
                }
            }
            break;
        }
        Ans = Ans + now;
        preSeg.emplace_back(i);
        if (now.Max >= l) {
            if (x < y) {
                int L = x, R = y;
                while (L <= R) {
                    int mid = L + R >> 1;
                    if (linkQuery(root[rt], 1, n, x, mid).Max >= l) R = mid - 1;
                    else L = mid + 1;
                }
                pos = id[R + 1 - l + 1];
            } else {
                int L = y, R = x;
                while (L <= R) {
                    int mid = L + R >> 1;
                    if (linkQuery(root[rt], 1, n, mid, x).Max >= l) L = mid + 1;
                    else R = mid - 1;
                }
                pos = id[L - 1 + l - 1];
            }
            break;
        }
    }
    cout << (pos ? dep[U] + dep[pos] - 2 * dep[lca(U, pos)] : -1) << '\n';
}

void solve() {
    cin >> n >> m;
    clear();
    for (int i = 1; i <= n; ++i) {
        cin >> a[i];
        tmp[a[i]].push_back(i);
    }
    for (int i = 1; i < n; ++i) {
        int u, v; cin >> u >> v;
        e[u].emplace_back(v); e[v].emplace_back(u);
    }
    dfs(1, 0); DFS(1, 1);
    build(root[n + 1], 1, n);
    for (int i = n; i >= 1; --i) {
        root[i] = root[i + 1];
        for (auto j : tmp[i])
            insert(root[i], root[i], 1, n, in[j]);
    }
    for (int i = 1; i <= m; ++i) {
        int op; cin >> op;
        if (op == 1) {
            int u, v, x; cin >> u >> v >> x;
            Copy(u, v, x + 1, x);
        } else if (op == 2) {
            int u, v, x; cin >> u >> v >> x;
            Copy(u, v, x, x + 1);
        } else {
            int u, v, l, y; cin >> u >> v >> l >> y;
            Query(u, v, y, l);
        }
    }
}
