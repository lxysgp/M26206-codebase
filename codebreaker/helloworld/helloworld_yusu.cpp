#include <algorithm>
#include <array>
#include <bitset>
#include <cassert>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <functional>
#include <iomanip>
#include <iostream>
#include <map>
#include <numeric>
#include <queue>
#include <random>
#include <set>
#include <tuple>
#include <vector>
#include <deque>
#include <list>
#include <bits/stdc++.h>
using namespace std;

typedef long long ll;
typedef vector<int> vi;
typedef vector<ll> vl;
typedef pair<int, int> pii;
typedef pair<ll, ll> pll;

#define endl '\n'
#define all(x) (x).begin(), (x).end()
#define rep(i, a, b) for (int i = (a); i < (b); i++)

const int MOD = 1e9 + 7;

class FastIO {
private:
    static const int BUFFER_SIZE = 1 << 16;
    char in_buffer[BUFFER_SIZE], out_buffer[BUFFER_SIZE];
    int in_pos = 0, in_len = 0, out_pos = 0;
    char get_char() {
        if (in_pos >= in_len) {
            in_len = fread(in_buffer, 1, BUFFER_SIZE, stdin);
            in_pos = 0;
            if (in_len == 0) return EOF;}
        return in_buffer[in_pos++];}
    template<typename T> void read_int(T &x) {
        x = 0; char c = get_char(); bool neg = false;
        while (c <= 32) c = get_char();
        if (c == '-') { neg = true; c = get_char(); }
        while (c >= '0' && c <= '9') { x = x * 10 + (c - '0'); c = get_char(); }
        if (neg) x = -x;}
    void read_string(string &s) {
        s.clear(); char c = get_char();
        while (c <= 32) c = get_char();
        while (c > 32) { s += c; c = get_char(); }}
    void flush() {
        if (out_pos) { fwrite(out_buffer, 1, out_pos, stdout); out_pos = 0; }}
    void put_char(char c) {
        if (out_pos >= BUFFER_SIZE) flush();
        out_buffer[out_pos++] = c;}
    template<typename T> void write_int(T x) {
        if (x < 0) { put_char('-'); x = -x; }
        char buffer[20]; int pos = 0;
        do { buffer[pos++] = '0' + (x % 10); x /= 10; } while (x > 0);
        while (pos > 0) put_char(buffer[--pos]);}
    void write_string(const string &s) {
        for (char c : s) put_char(c);
    }
public:
    FastIO() {}
    ~FastIO() { flush(); }
    int ri() { int x; read_int(x); return x; }
    ll rl() { ll x; read_int(x); return x; }
    string rs() { string s; read_string(s); return s; }
    void pi(int x) { write_int(x); put_char('\n'); }
    void pl(ll x) { write_int(x); put_char('\n'); }
    void ps(const string &s) { write_string(s); put_char('\n'); }
};

FastIO fast_io;
#define ri fast_io.ri()
#define rl fast_io.rl()
#define rs fast_io.rs()

ll nCr(int n, int r) {
    if (r < 0 || r > n) return 0;
    r = min(r, n - r); 
    
    ll res = 1;
    for (int i = 1; i <= r; i++) {
        res = res * (n - i + 1) / i;
    }
    return res;
}

bool is_prime(ll n) {
    if (n < 2) return false;
    for (ll p = 2; p * p <= n; p++)
        if (n % p == 0) return false;
    return true;
}

ll gcd(ll a, ll b) { 
    while (b) { ll t = b; b = a % b; a = t; }
    return a;
}

ll lcm(ll a, ll b) { 
    return a / gcd(a, b) * b; 
}

vector<ll> fact, inv_fact;


string add_strings(const string &a, const string &b) {
    string res;
    int i = a.size() - 1, j = b.size() - 1, carry = 0;
    while (i >= 0 || j >= 0 || carry) {
        int sum = carry;
        if (i >= 0) sum += a[i--] - '0';
        if (j >= 0) sum += b[j--] - '0';
        carry = sum / 10;
        res.push_back('0' + (sum % 10));
    }
    reverse(all(res));
    return res;
}
string multiply_strings(const string &a, const string &b) {
    if (a == "0" || b == "0") return "0";
    int n = a.size(), m = b.size();
    vector<int> res(n + m, 0);
    for (int i = n - 1; i >= 0; i--) {
        for (int j = m - 1; j >= 0; j--) {
            int prod = (a[i] - '0') * (b[j] - '0');
            int sum = prod + res[i + j + 1];
            res[i + j + 1] = sum % 10;
            res[i + j] += sum / 10;
        }
    }
    string result;
    for (int num : res) {
        if (!(result.empty() && num == 0)) result.push_back('0' + num);
    }
    return result.empty() ? "0" : result;
}

bool compare_strings(const string &a, const string &b) {
    if (a.size() != b.size()) return a.size() < b.size();
    return a < b;
}

string subtract_strings(string a, string b) {
    if (compare_strings(a, b)) return "-" + subtract_strings(b, a);
    string res;
    int i = a.size() - 1, j = b.size() - 1, borrow = 0;
    while (i >= 0) {
        int digit_a = a[i--] - '0' - borrow;
        int digit_b = j >= 0 ? b[j--] - '0' : 0;
        if (digit_a < digit_b) { digit_a += 10; borrow = 1; } 
        else borrow = 0;
        res.push_back('0' + (digit_a - digit_b));
    }
    while (res.size() > 1 && res.back() == '0') res.pop_back();
    reverse(all(res));
    return res;
}

string mod_string(const string &num, int mod) {
    int res = 0;
    for (char c : num) res = (res * 10 + (c - '0')) % mod;
    return to_string(res);
}

vector<int> prefix_function(const string &s) {
    int n = s.size();
    vector<int> pi(n);
    rep(i, 1, n) {
        int j = pi[i - 1];
        while (j > 0 && s[i] != s[j]) j = pi[j - 1];
        if (s[i] == s[j]) j++;
        pi[i] = j;
    }
    return pi;
}
vector<int> z_function(const string &s) {
    int n = s.size();
    vector<int> z(n);
    for (int i = 1, l = 0, r = 0; i < n; i++) {
        if (i <= r) z[i] = min(r - i + 1, z[i - l]);
        while (i + z[i] < n && s[z[i]] == s[i + z[i]]) z[i]++;
        if (i + z[i] - 1 > r) { l = i; r = i + z[i] - 1; }
    }
    return z;
}
class StringHasher {
private:
    const ll base = 911382323, mod = 1e9 + 7;
    vector<ll> pow_base, prefix_hash;
public:
    void build(const string &s) {
        int n = s.size();
        pow_base.resize(n + 1); prefix_hash.resize(n + 1);
        pow_base[0] = 1; prefix_hash[0] = 0;
        rep(i, 0, n) {
            pow_base[i + 1] = (pow_base[i] * base) % mod;
            prefix_hash[i + 1] = (prefix_hash[i] * base + s[i]) % mod;
        }
    }
    ll get_hash(int l, int r) {
        ll hash_val = (prefix_hash[r + 1] - prefix_hash[l] * pow_base[r - l + 1]) % mod;
        return hash_val < 0 ? hash_val + mod : hash_val;}
};
template<class Fun>
class y_combinator_result {
    Fun fun_;
public:
    template<class T> explicit y_combinator_result(T &&fun): fun_(std::forward<T>(fun)) {}
    template<class ...Args> decltype(auto) operator()(Args &&...args) { 
        return fun_(std::ref(*this), std::forward<Args>(args)...); }};
template<class Fun>
decltype(auto) y_combinator(Fun &&fun) { 
    return y_combinator_result<std::decay_t<Fun>>(std::forward<Fun>(fun)); }
#ifdef DEBUG
#define dbg(x) cerr << #x << " = " << (x) << endl
#else
#define dbg(x)
#endif

/////////////////////////////////////////////////////////

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);
    auto power_recursive = y_combinator([](auto self, ll a, ll b) -> ll {
        if (b == 0) return 1;
        ll half = self(a, b / 2);
        return half * half * (b % 2 ? a : 1);
    });
    fast_io.ps("Hello World");
    return 0;
}
