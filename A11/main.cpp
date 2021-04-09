#include <iostream>
#include <map>
#include <list>
#include <vector>
#include <gmpxx.h>
#include <algorithm>
#include <string>
#include <iterator>
#include "partition.h"
#include "calc_z.h"
#include "split.h"

using std::cout;      using std::endl;
using std::pair;      using std::list;
using std::map;       using std::ostream;
using std::vector;    using std::max;
using std::string;    using std::cin;
using std::stoi;      using std::to_string;
using std::transform;
using partition::Par; using partition::generate;

using QQ = mpq_class;
using Q = int;
using s = pair<int, Q>;
using monomial = pair<list<s>, Q>;
using V = map<monomial, QQ>;

ostream& operator << (ostream& os, const s& x)
{
  return os << "(" << x.first << ", " << x.second << ")";
}

ostream& operator << (ostream& os, const list<s>& l)
{
  os << "[";
  for(typename list<s>::const_iterator iter = l.begin();
      iter != l.end(); ++iter) {
    if(iter != l.begin()) os << ", ";
    os << (*iter);
  }
  return os << "]";
}

ostream& operator << (ostream& os, const monomial& m)
{
  return os << "[" << m.first << ", " << m.second << "]";
}

ostream& operator << (ostream& os, const V& v)
{
  os << "[";
  for(V::const_iterator iter = v.begin();
      iter != v.end(); ++iter) {
    if(iter != v.begin()) os << ", ";
    os << "["
       << iter -> first << ", "
       << iter -> second
       << "]";
  }
  return os << "]";
}

V& omit(V& v)
{
  for(V::const_iterator iter = v.begin();
      iter != v.end();) {
    if(iter -> second == 0)
      iter = v.erase(iter);
    else
      ++iter;
  }
  return v;
}

V& add (V& v, const V& v1)
{
  V& ret = v;
  for(V::const_iterator iter = v1.begin();
      iter != v1.end(); ++iter) {
    V::iterator it = ret.find(iter -> first);
    if(it != ret.end()) {
      it -> second += iter -> second;
    }
    else
      ret.insert(*iter);
  }

  return omit(ret);
}

int sum(const monomial& m)
{
  int ret = 0;
  list<s> l = m.first;
  for(list<s>::const_iterator iter = l.begin();
      iter != l.end(); ++iter) {
    ret += -(iter -> first);
  }
  return ret;
}

int max(const V& v)
{
  int ret = 0;
  for(V::const_iterator iter = v.begin();
      iter != v.end(); ++iter) {
    ret = max(ret, sum(iter -> first));
  }
  return ret;
}

list<s> append(const s& x, list<s> l)
{
  l.push_front(x);
  l.sort();
  return l;
}

V append(const s& x, const V& v)
{
  V ret;
  for(V::const_iterator iter = v.begin();
      iter != v.end(); ++iter) {
    const monomial& m = iter -> first;
    ret.insert(
      make_pair(
        make_pair(append(x, m.first), m.second),
        iter -> second)
      );
  }
  return ret;
}

V append(const Par& p, Q gamma, const pair<monomial, QQ>& v)
{
  V ret;
  ret.insert(v);
  for(Par::const_iterator it = p.begin();
      it != p.end(); ++it) {
    ret = append(s(-(*it), gamma), ret);
  }
  return ret;
}

int inner(Q x, Q y)
{
  return 2 * x * y;
}

V dh(Q gamma, const V& v)
{
  V ret;
  for(V::const_iterator iter = v.begin();
      iter != v.end(); ++iter) {
    Q beta = (iter -> first).second;
    ret[iter -> first] = iter -> second * inner(gamma, beta);
  }
  return omit(ret);
}

V d(const s& x, const pair<monomial, QQ> v)
{
  if(v.first.first.empty())
    return V();
  V ret;
  const monomial& m = v.first;
  list<s> l = m.first;
  const s head = l.front();
  if(head.first == -x.first) {
    l.pop_front();
    ret[monomial(l, m.second)] = v.second * x.first * inner(x.second, head.second);
  }

  pair<monomial, QQ> n_v = v;
  n_v.first.first.pop_front();

  return add(ret, append(head, d(x, n_v)));
}

V d(const s& x, const V& v)
{
  V ret;
  for(V::const_iterator iter = v.begin();
      iter != v.end(); ++iter) {
    ret = add(ret, d(x, *iter));
  }
  return omit(ret);
}

V d(const Par& p, Q gamma, const pair<monomial, QQ>& v)
{
  V ret;
  ret.insert(v);
  for(Par::const_iterator it = p.begin();
      it != p.end(); ++it) {
    ret = d(s(*it, gamma), ret);
  }
  return omit(ret);
}

V operator * (const s& x, const V& v)
{
  if (x.first < 0)
    return append(x, v);
  if (x.first == 0)
    return dh(x.second, v);
  return d(x, v);
}

V operator * (const QQ& a, const V& v)
{
  V ret = v;
  for(V::iterator iter = ret.begin();
        iter != ret.end(); ++iter)
    iter -> second *= a;
  return ret;
}

int eps(Q x, Q y)
{
  return 1;
}

V e(Q x, const V& v)
{
  V ret;
  for(V::const_iterator iter = v.begin();
      iter != v.end(); ++iter) {
    Q g = (iter -> first).second + x;
    ret[V::key_type((iter -> first).first, g)] =
      (iter -> second) * eps((iter -> first).second, x);
  }
  return ret;
}

V c(Q x, const V& v)
{
  V ret;
  for(V::const_iterator iter = v.begin();
      iter != v.end(); ++iter) {
    ret[V::key_type(iter -> first)] =
      (iter -> second) * eps((iter -> first).second, x);
  }
  return ret;
}

V exp_plus(int k, Q gamma, const pair<monomial, QQ>& v)
{
  if(k > 0) return V();
  V ret;
  vector<Par> pars;
  generate(-k, pars);
  for(vector<Par>::const_iterator it = pars.begin();
      it != pars.end(); ++it) {
    ret = add(ret,
              QQ(partition::l(*it) % 2 == 0 ? 1 : -1) *
              (QQ(1) / QQ(z(*it))) *
              (d(*it, gamma, v))
             );
  }
  return omit(ret);
}

V exp_plus(int k, Q gamma, const V& v)
{
  if(k > 0) return V();
  V ret;
  for(V::const_iterator iter = v.begin();
      iter != v.end(); ++iter)
    ret = add(ret, exp_plus(k, gamma, *iter));
  return omit(ret);
}

V exp_minus(int k, Q gamma, const pair<monomial, QQ>& v)
{
  if(k < 0) return V();
  V ret;
  vector<Par> pars;
  generate(k, pars);
  for(vector<Par>::const_iterator it = pars.begin();
      it != pars.end(); ++it) {
    ret = add(ret,
              (QQ(1) / QQ(z(*it))) *
              (append(*it, gamma, v))
             );
  }
  return omit(ret);
}

V exp_minus(int k, Q gamma, const V& v)
{
  if(k < 0) return V();
  V ret;
  for(V::const_iterator iter = v.begin();
      iter != v.end(); ++iter)
    ret = add(ret, exp_minus(k, gamma, *iter));
  return omit(ret);
}

V X(int k, Q gamma, const V& v)
{
  V ret;
  for(V::const_iterator iter = v.begin();
      iter != v.end(); ++iter) {
    const monomial& m = iter -> first;
    V tmp;
    tmp.insert(*iter);
    int ev = k - inner(gamma, gamma) / 2 - inner(gamma, m.second);
    tmp = e(gamma, tmp);
    for(int i = 0; i <= max(v); i++) { 
      ret = add(ret, exp_minus(ev + i, gamma, exp_plus(-i, gamma, tmp)));
    }
  }
  return ret;
}

V E(int k, Q gamma, const V& v)
{
  return X(-k, gamma, c(gamma, v));
}

string Es_str(const vector<int>& in, string v)
{
  if(in.empty()) return v;
  string ret = "[";
  for(vector<int>::const_iterator iter = in.begin();
        iter != in.end(); ++iter) {
    if(iter != in.begin()) ret += ", ";
    ret += "(" + to_string(*iter) + ", 1)";
  }
  return ret + "] * v";
}

V Es(const vector<int>& in, const V& v)
{
  V ret = v;
  // in の 後ろから順に作用させる
  for(vector<int>::const_reverse_iterator iter = in.rbegin();
        iter != in.rend(); ++iter) {
    ret = E(*iter, 1, ret);
  }
  return ret;
}

vector<int> stoi(const vector<string>& strs)
{
  vector<int> ret;
  transform(strs.begin(), strs.end(), back_inserter(ret), [](string s){return stoi(s);});
  return ret;
}


int main()
{
  V v;
  v[V::key_type(list<s>(), 0)] = 1;
  cout << "v = " <<  v << endl;
/*  string str;
  while(getline(cin, str)) {
    vector<string> strs = split(str);
    vector<int> in = stoi(strs);
    V result = Es(in, v);
    cout << Es_str(in, "v") << "=" << endl
         << result << endl;
  }*/
  // now 1.36 sec
  cout << "E(-10, 1, E(-9, 1,  v)) = "
       << E(-10, 1, E(-9, 1, v)) << endl;
  return 0;
}
