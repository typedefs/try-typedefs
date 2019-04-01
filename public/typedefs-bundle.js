(function(){function r(e,n,t){function o(i,f){if(!n[i]){if(!e[i]){var c="function"==typeof require&&require;if(!f&&c)return c(i,!0);if(u)return u(i,!0);var a=new Error("Cannot find module '"+i+"'");throw a.code="MODULE_NOT_FOUND",a}var p=n[i]={exports:{}};e[i][0].call(p.exports,function(r){var n=e[i][1][r];return o(n||r)},p,p.exports,r,e,n,t)}return n[i].exports}for(var u="function"==typeof require&&require,i=0;i<t.length;i++)o(t[i]);return o}return r})()({1:[function(require,module,exports){
(function (process,Buffer){
"use strict";

(function(){

const $JSRTS = {
    throw: function (x) {
        throw x;
    },
    Lazy: function (e) {
        this.js_idris_lazy_calc = e;
        this.js_idris_lazy_val = void 0;
    },
    force: function (x) {
        if (x === undefined || x.js_idris_lazy_calc === undefined) {
            return x
        } else {
            if (x.js_idris_lazy_val === undefined) {
                x.js_idris_lazy_val = x.js_idris_lazy_calc()
            }
            return x.js_idris_lazy_val
        }
    },
    prim_strSubstr: function (offset, len, str) {
        return str.substr(Math.max(0, offset), Math.max(0, len))
    }
};
$JSRTS.os = require('os');

$JSRTS.fs = require('fs');

$JSRTS.prim_systemInfo = function (index) {
    switch (index) {
        case 0:
            return "node";
        case 1:
            return $JSRTS.os.platform();
    }
    return "";
};

$JSRTS.prim_writeStr = function (x) { return process.stdout.write(x) };

$JSRTS.prim_readStr = function () {
    var ret = '';
    var b = new Buffer(1024);
    var i = 0;
    while (true) {
        $JSRTS.fs.readSync(0, b, i, 1)
        if (b[i] == 10) {
            ret = b.toString('utf8', 0, i);
            break;
        }
        i++;
        if (i == b.length) {
            var nb = new Buffer(b.length * 2);
            b.copy(nb)
            b = nb;
        }
    }
    return ret;
};

$JSRTS.die = function (message) {
    console.error(message);
    process.exit(-1);
};
$JSRTS.jsbn = (function () {

  // Copyright (c) 2005  Tom Wu
  // All Rights Reserved.
  // See "LICENSE" for details.

  // Basic JavaScript BN library - subset useful for RSA encryption.

  // Bits per digit
  var dbits;

  // JavaScript engine analysis
  var canary = 0xdeadbeefcafe;
  var j_lm = ((canary & 0xffffff) == 0xefcafe);

  // (public) Constructor
  function BigInteger(a, b, c) {
    if (a != null)
      if ("number" == typeof a) this.fromNumber(a, b, c);
      else if (b == null && "string" != typeof a) this.fromString(a, 256);
      else this.fromString(a, b);
  }

  // return new, unset BigInteger
  function nbi() { return new BigInteger(null); }

  // am: Compute w_j += (x*this_i), propagate carries,
  // c is initial carry, returns final carry.
  // c < 3*dvalue, x < 2*dvalue, this_i < dvalue
  // We need to select the fastest one that works in this environment.

  // am1: use a single mult and divide to get the high bits,
  // max digit bits should be 26 because
  // max internal value = 2*dvalue^2-2*dvalue (< 2^53)
  function am1(i, x, w, j, c, n) {
    while (--n >= 0) {
      var v = x * this[i++] + w[j] + c;
      c = Math.floor(v / 0x4000000);
      w[j++] = v & 0x3ffffff;
    }
    return c;
  }
  // am2 avoids a big mult-and-extract completely.
  // Max digit bits should be <= 30 because we do bitwise ops
  // on values up to 2*hdvalue^2-hdvalue-1 (< 2^31)
  function am2(i, x, w, j, c, n) {
    var xl = x & 0x7fff, xh = x >> 15;
    while (--n >= 0) {
      var l = this[i] & 0x7fff;
      var h = this[i++] >> 15;
      var m = xh * l + h * xl;
      l = xl * l + ((m & 0x7fff) << 15) + w[j] + (c & 0x3fffffff);
      c = (l >>> 30) + (m >>> 15) + xh * h + (c >>> 30);
      w[j++] = l & 0x3fffffff;
    }
    return c;
  }
  // Alternately, set max digit bits to 28 since some
  // browsers slow down when dealing with 32-bit numbers.
  function am3(i, x, w, j, c, n) {
    var xl = x & 0x3fff, xh = x >> 14;
    while (--n >= 0) {
      var l = this[i] & 0x3fff;
      var h = this[i++] >> 14;
      var m = xh * l + h * xl;
      l = xl * l + ((m & 0x3fff) << 14) + w[j] + c;
      c = (l >> 28) + (m >> 14) + xh * h;
      w[j++] = l & 0xfffffff;
    }
    return c;
  }
  var inBrowser = typeof navigator !== "undefined";
  if (inBrowser && j_lm && (navigator.appName == "Microsoft Internet Explorer")) {
    BigInteger.prototype.am = am2;
    dbits = 30;
  }
  else if (inBrowser && j_lm && (navigator.appName != "Netscape")) {
    BigInteger.prototype.am = am1;
    dbits = 26;
  }
  else { // Mozilla/Netscape seems to prefer am3
    BigInteger.prototype.am = am3;
    dbits = 28;
  }

  BigInteger.prototype.DB = dbits;
  BigInteger.prototype.DM = ((1 << dbits) - 1);
  BigInteger.prototype.DV = (1 << dbits);

  var BI_FP = 52;
  BigInteger.prototype.FV = Math.pow(2, BI_FP);
  BigInteger.prototype.F1 = BI_FP - dbits;
  BigInteger.prototype.F2 = 2 * dbits - BI_FP;

  // Digit conversions
  var BI_RM = "0123456789abcdefghijklmnopqrstuvwxyz";
  var BI_RC = new Array();
  var rr, vv;
  rr = "0".charCodeAt(0);
  for (vv = 0; vv <= 9; ++vv) BI_RC[rr++] = vv;
  rr = "a".charCodeAt(0);
  for (vv = 10; vv < 36; ++vv) BI_RC[rr++] = vv;
  rr = "A".charCodeAt(0);
  for (vv = 10; vv < 36; ++vv) BI_RC[rr++] = vv;

  function int2char(n) { return BI_RM.charAt(n); }
  function intAt(s, i) {
    var c = BI_RC[s.charCodeAt(i)];
    return (c == null) ? -1 : c;
  }

  // (protected) copy this to r
  function bnpCopyTo(r) {
    for (var i = this.t - 1; i >= 0; --i) r[i] = this[i];
    r.t = this.t;
    r.s = this.s;
  }

  // (protected) set from integer value x, -DV <= x < DV
  function bnpFromInt(x) {
    this.t = 1;
    this.s = (x < 0) ? -1 : 0;
    if (x > 0) this[0] = x;
    else if (x < -1) this[0] = x + this.DV;
    else this.t = 0;
  }

  // return bigint initialized to value
  function nbv(i) { var r = nbi(); r.fromInt(i); return r; }

  // (protected) set from string and radix
  function bnpFromString(s, b) {
    var k;
    if (b == 16) k = 4;
    else if (b == 8) k = 3;
    else if (b == 256) k = 8; // byte array
    else if (b == 2) k = 1;
    else if (b == 32) k = 5;
    else if (b == 4) k = 2;
    else { this.fromRadix(s, b); return; }
    this.t = 0;
    this.s = 0;
    var i = s.length, mi = false, sh = 0;
    while (--i >= 0) {
      var x = (k == 8) ? s[i] & 0xff : intAt(s, i);
      if (x < 0) {
        if (s.charAt(i) == "-") mi = true;
        continue;
      }
      mi = false;
      if (sh == 0)
        this[this.t++] = x;
      else if (sh + k > this.DB) {
        this[this.t - 1] |= (x & ((1 << (this.DB - sh)) - 1)) << sh;
        this[this.t++] = (x >> (this.DB - sh));
      }
      else
        this[this.t - 1] |= x << sh;
      sh += k;
      if (sh >= this.DB) sh -= this.DB;
    }
    if (k == 8 && (s[0] & 0x80) != 0) {
      this.s = -1;
      if (sh > 0) this[this.t - 1] |= ((1 << (this.DB - sh)) - 1) << sh;
    }
    this.clamp();
    if (mi) BigInteger.ZERO.subTo(this, this);
  }

  // (protected) clamp off excess high words
  function bnpClamp() {
    var c = this.s & this.DM;
    while (this.t > 0 && this[this.t - 1] == c)--this.t;
  }

  // (public) return string representation in given radix
  function bnToString(b) {
    if (this.s < 0) return "-" + this.negate().toString(b);
    var k;
    if (b == 16) k = 4;
    else if (b == 8) k = 3;
    else if (b == 2) k = 1;
    else if (b == 32) k = 5;
    else if (b == 4) k = 2;
    else return this.toRadix(b);
    var km = (1 << k) - 1, d, m = false, r = "", i = this.t;
    var p = this.DB - (i * this.DB) % k;
    if (i-- > 0) {
      if (p < this.DB && (d = this[i] >> p) > 0) { m = true; r = int2char(d); }
      while (i >= 0) {
        if (p < k) {
          d = (this[i] & ((1 << p) - 1)) << (k - p);
          d |= this[--i] >> (p += this.DB - k);
        }
        else {
          d = (this[i] >> (p -= k)) & km;
          if (p <= 0) { p += this.DB; --i; }
        }
        if (d > 0) m = true;
        if (m) r += int2char(d);
      }
    }
    return m ? r : "0";
  }

  // (public) -this
  function bnNegate() { var r = nbi(); BigInteger.ZERO.subTo(this, r); return r; }

  // (public) |this|
  function bnAbs() { return (this.s < 0) ? this.negate() : this; }

  // (public) return + if this > a, - if this < a, 0 if equal
  function bnCompareTo(a) {
    var r = this.s - a.s;
    if (r != 0) return r;
    var i = this.t;
    r = i - a.t;
    if (r != 0) return (this.s < 0) ? -r : r;
    while (--i >= 0) if ((r = this[i] - a[i]) != 0) return r;
    return 0;
  }

  // returns bit length of the integer x
  function nbits(x) {
    var r = 1, t;
    if ((t = x >>> 16) != 0) { x = t; r += 16; }
    if ((t = x >> 8) != 0) { x = t; r += 8; }
    if ((t = x >> 4) != 0) { x = t; r += 4; }
    if ((t = x >> 2) != 0) { x = t; r += 2; }
    if ((t = x >> 1) != 0) { x = t; r += 1; }
    return r;
  }

  // (public) return the number of bits in "this"
  function bnBitLength() {
    if (this.t <= 0) return 0;
    return this.DB * (this.t - 1) + nbits(this[this.t - 1] ^ (this.s & this.DM));
  }

  // (protected) r = this << n*DB
  function bnpDLShiftTo(n, r) {
    var i;
    for (i = this.t - 1; i >= 0; --i) r[i + n] = this[i];
    for (i = n - 1; i >= 0; --i) r[i] = 0;
    r.t = this.t + n;
    r.s = this.s;
  }

  // (protected) r = this >> n*DB
  function bnpDRShiftTo(n, r) {
    for (var i = n; i < this.t; ++i) r[i - n] = this[i];
    r.t = Math.max(this.t - n, 0);
    r.s = this.s;
  }

  // (protected) r = this << n
  function bnpLShiftTo(n, r) {
    var bs = n % this.DB;
    var cbs = this.DB - bs;
    var bm = (1 << cbs) - 1;
    var ds = Math.floor(n / this.DB), c = (this.s << bs) & this.DM, i;
    for (i = this.t - 1; i >= 0; --i) {
      r[i + ds + 1] = (this[i] >> cbs) | c;
      c = (this[i] & bm) << bs;
    }
    for (i = ds - 1; i >= 0; --i) r[i] = 0;
    r[ds] = c;
    r.t = this.t + ds + 1;
    r.s = this.s;
    r.clamp();
  }

  // (protected) r = this >> n
  function bnpRShiftTo(n, r) {
    r.s = this.s;
    var ds = Math.floor(n / this.DB);
    if (ds >= this.t) { r.t = 0; return; }
    var bs = n % this.DB;
    var cbs = this.DB - bs;
    var bm = (1 << bs) - 1;
    r[0] = this[ds] >> bs;
    for (var i = ds + 1; i < this.t; ++i) {
      r[i - ds - 1] |= (this[i] & bm) << cbs;
      r[i - ds] = this[i] >> bs;
    }
    if (bs > 0) r[this.t - ds - 1] |= (this.s & bm) << cbs;
    r.t = this.t - ds;
    r.clamp();
  }

  // (protected) r = this - a
  function bnpSubTo(a, r) {
    var i = 0, c = 0, m = Math.min(a.t, this.t);
    while (i < m) {
      c += this[i] - a[i];
      r[i++] = c & this.DM;
      c >>= this.DB;
    }
    if (a.t < this.t) {
      c -= a.s;
      while (i < this.t) {
        c += this[i];
        r[i++] = c & this.DM;
        c >>= this.DB;
      }
      c += this.s;
    }
    else {
      c += this.s;
      while (i < a.t) {
        c -= a[i];
        r[i++] = c & this.DM;
        c >>= this.DB;
      }
      c -= a.s;
    }
    r.s = (c < 0) ? -1 : 0;
    if (c < -1) r[i++] = this.DV + c;
    else if (c > 0) r[i++] = c;
    r.t = i;
    r.clamp();
  }

  // (protected) r = this * a, r != this,a (HAC 14.12)
  // "this" should be the larger one if appropriate.
  function bnpMultiplyTo(a, r) {
    var x = this.abs(), y = a.abs();
    var i = x.t;
    r.t = i + y.t;
    while (--i >= 0) r[i] = 0;
    for (i = 0; i < y.t; ++i) r[i + x.t] = x.am(0, y[i], r, i, 0, x.t);
    r.s = 0;
    r.clamp();
    if (this.s != a.s) BigInteger.ZERO.subTo(r, r);
  }

  // (protected) r = this^2, r != this (HAC 14.16)
  function bnpSquareTo(r) {
    var x = this.abs();
    var i = r.t = 2 * x.t;
    while (--i >= 0) r[i] = 0;
    for (i = 0; i < x.t - 1; ++i) {
      var c = x.am(i, x[i], r, 2 * i, 0, 1);
      if ((r[i + x.t] += x.am(i + 1, 2 * x[i], r, 2 * i + 1, c, x.t - i - 1)) >= x.DV) {
        r[i + x.t] -= x.DV;
        r[i + x.t + 1] = 1;
      }
    }
    if (r.t > 0) r[r.t - 1] += x.am(i, x[i], r, 2 * i, 0, 1);
    r.s = 0;
    r.clamp();
  }

  // (protected) divide this by m, quotient and remainder to q, r (HAC 14.20)
  // r != q, this != m.  q or r may be null.
  function bnpDivRemTo(m, q, r) {
    var pm = m.abs();
    if (pm.t <= 0) return;
    var pt = this.abs();
    if (pt.t < pm.t) {
      if (q != null) q.fromInt(0);
      if (r != null) this.copyTo(r);
      return;
    }
    if (r == null) r = nbi();
    var y = nbi(), ts = this.s, ms = m.s;
    var nsh = this.DB - nbits(pm[pm.t - 1]);   // normalize modulus
    if (nsh > 0) { pm.lShiftTo(nsh, y); pt.lShiftTo(nsh, r); }
    else { pm.copyTo(y); pt.copyTo(r); }
    var ys = y.t;
    var y0 = y[ys - 1];
    if (y0 == 0) return;
    var yt = y0 * (1 << this.F1) + ((ys > 1) ? y[ys - 2] >> this.F2 : 0);
    var d1 = this.FV / yt, d2 = (1 << this.F1) / yt, e = 1 << this.F2;
    var i = r.t, j = i - ys, t = (q == null) ? nbi() : q;
    y.dlShiftTo(j, t);
    if (r.compareTo(t) >= 0) {
      r[r.t++] = 1;
      r.subTo(t, r);
    }
    BigInteger.ONE.dlShiftTo(ys, t);
    t.subTo(y, y);  // "negative" y so we can replace sub with am later
    while (y.t < ys) y[y.t++] = 0;
    while (--j >= 0) {
      // Estimate quotient digit
      var qd = (r[--i] == y0) ? this.DM : Math.floor(r[i] * d1 + (r[i - 1] + e) * d2);
      if ((r[i] += y.am(0, qd, r, j, 0, ys)) < qd) {   // Try it out
        y.dlShiftTo(j, t);
        r.subTo(t, r);
        while (r[i] < --qd) r.subTo(t, r);
      }
    }
    if (q != null) {
      r.drShiftTo(ys, q);
      if (ts != ms) BigInteger.ZERO.subTo(q, q);
    }
    r.t = ys;
    r.clamp();
    if (nsh > 0) r.rShiftTo(nsh, r); // Denormalize remainder
    if (ts < 0) BigInteger.ZERO.subTo(r, r);
  }

  // (public) this mod a
  function bnMod(a) {
    var r = nbi();
    this.abs().divRemTo(a, null, r);
    if (this.s < 0 && r.compareTo(BigInteger.ZERO) > 0) a.subTo(r, r);
    return r;
  }

  // Modular reduction using "classic" algorithm
  function Classic(m) { this.m = m; }
  function cConvert(x) {
    if (x.s < 0 || x.compareTo(this.m) >= 0) return x.mod(this.m);
    else return x;
  }
  function cRevert(x) { return x; }
  function cReduce(x) { x.divRemTo(this.m, null, x); }
  function cMulTo(x, y, r) { x.multiplyTo(y, r); this.reduce(r); }
  function cSqrTo(x, r) { x.squareTo(r); this.reduce(r); }

  Classic.prototype.convert = cConvert;
  Classic.prototype.revert = cRevert;
  Classic.prototype.reduce = cReduce;
  Classic.prototype.mulTo = cMulTo;
  Classic.prototype.sqrTo = cSqrTo;

  // (protected) return "-1/this % 2^DB"; useful for Mont. reduction
  // justification:
  //         xy == 1 (mod m)
  //         xy =  1+km
  //   xy(2-xy) = (1+km)(1-km)
  // x[y(2-xy)] = 1-k^2m^2
  // x[y(2-xy)] == 1 (mod m^2)
  // if y is 1/x mod m, then y(2-xy) is 1/x mod m^2
  // should reduce x and y(2-xy) by m^2 at each step to keep size bounded.
  // JS multiply "overflows" differently from C/C++, so care is needed here.
  function bnpInvDigit() {
    if (this.t < 1) return 0;
    var x = this[0];
    if ((x & 1) == 0) return 0;
    var y = x & 3;       // y == 1/x mod 2^2
    y = (y * (2 - (x & 0xf) * y)) & 0xf; // y == 1/x mod 2^4
    y = (y * (2 - (x & 0xff) * y)) & 0xff;   // y == 1/x mod 2^8
    y = (y * (2 - (((x & 0xffff) * y) & 0xffff))) & 0xffff;    // y == 1/x mod 2^16
    // last step - calculate inverse mod DV directly;
    // assumes 16 < DB <= 32 and assumes ability to handle 48-bit ints
    y = (y * (2 - x * y % this.DV)) % this.DV;       // y == 1/x mod 2^dbits
    // we really want the negative inverse, and -DV < y < DV
    return (y > 0) ? this.DV - y : -y;
  }

  // Montgomery reduction
  function Montgomery(m) {
    this.m = m;
    this.mp = m.invDigit();
    this.mpl = this.mp & 0x7fff;
    this.mph = this.mp >> 15;
    this.um = (1 << (m.DB - 15)) - 1;
    this.mt2 = 2 * m.t;
  }

  // xR mod m
  function montConvert(x) {
    var r = nbi();
    x.abs().dlShiftTo(this.m.t, r);
    r.divRemTo(this.m, null, r);
    if (x.s < 0 && r.compareTo(BigInteger.ZERO) > 0) this.m.subTo(r, r);
    return r;
  }

  // x/R mod m
  function montRevert(x) {
    var r = nbi();
    x.copyTo(r);
    this.reduce(r);
    return r;
  }

  // x = x/R mod m (HAC 14.32)
  function montReduce(x) {
    while (x.t <= this.mt2) // pad x so am has enough room later
      x[x.t++] = 0;
    for (var i = 0; i < this.m.t; ++i) {
      // faster way of calculating u0 = x[i]*mp mod DV
      var j = x[i] & 0x7fff;
      var u0 = (j * this.mpl + (((j * this.mph + (x[i] >> 15) * this.mpl) & this.um) << 15)) & x.DM;
      // use am to combine the multiply-shift-add into one call
      j = i + this.m.t;
      x[j] += this.m.am(0, u0, x, i, 0, this.m.t);
      // propagate carry
      while (x[j] >= x.DV) { x[j] -= x.DV; x[++j]++; }
    }
    x.clamp();
    x.drShiftTo(this.m.t, x);
    if (x.compareTo(this.m) >= 0) x.subTo(this.m, x);
  }

  // r = "x^2/R mod m"; x != r
  function montSqrTo(x, r) { x.squareTo(r); this.reduce(r); }

  // r = "xy/R mod m"; x,y != r
  function montMulTo(x, y, r) { x.multiplyTo(y, r); this.reduce(r); }

  Montgomery.prototype.convert = montConvert;
  Montgomery.prototype.revert = montRevert;
  Montgomery.prototype.reduce = montReduce;
  Montgomery.prototype.mulTo = montMulTo;
  Montgomery.prototype.sqrTo = montSqrTo;

  // (protected) true iff this is even
  function bnpIsEven() { return ((this.t > 0) ? (this[0] & 1) : this.s) == 0; }

  // (protected) this^e, e < 2^32, doing sqr and mul with "r" (HAC 14.79)
  function bnpExp(e, z) {
    if (e > 0xffffffff || e < 1) return BigInteger.ONE;
    var r = nbi(), r2 = nbi(), g = z.convert(this), i = nbits(e) - 1;
    g.copyTo(r);
    while (--i >= 0) {
      z.sqrTo(r, r2);
      if ((e & (1 << i)) > 0) z.mulTo(r2, g, r);
      else { var t = r; r = r2; r2 = t; }
    }
    return z.revert(r);
  }

  // (public) this^e % m, 0 <= e < 2^32
  function bnModPowInt(e, m) {
    var z;
    if (e < 256 || m.isEven()) z = new Classic(m); else z = new Montgomery(m);
    return this.exp(e, z);
  }

  // protected
  BigInteger.prototype.copyTo = bnpCopyTo;
  BigInteger.prototype.fromInt = bnpFromInt;
  BigInteger.prototype.fromString = bnpFromString;
  BigInteger.prototype.clamp = bnpClamp;
  BigInteger.prototype.dlShiftTo = bnpDLShiftTo;
  BigInteger.prototype.drShiftTo = bnpDRShiftTo;
  BigInteger.prototype.lShiftTo = bnpLShiftTo;
  BigInteger.prototype.rShiftTo = bnpRShiftTo;
  BigInteger.prototype.subTo = bnpSubTo;
  BigInteger.prototype.multiplyTo = bnpMultiplyTo;
  BigInteger.prototype.squareTo = bnpSquareTo;
  BigInteger.prototype.divRemTo = bnpDivRemTo;
  BigInteger.prototype.invDigit = bnpInvDigit;
  BigInteger.prototype.isEven = bnpIsEven;
  BigInteger.prototype.exp = bnpExp;

  // public
  BigInteger.prototype.toString = bnToString;
  BigInteger.prototype.negate = bnNegate;
  BigInteger.prototype.abs = bnAbs;
  BigInteger.prototype.compareTo = bnCompareTo;
  BigInteger.prototype.bitLength = bnBitLength;
  BigInteger.prototype.mod = bnMod;
  BigInteger.prototype.modPowInt = bnModPowInt;

  // "constants"
  BigInteger.ZERO = nbv(0);
  BigInteger.ONE = nbv(1);

  // Copyright (c) 2005-2009  Tom Wu
  // All Rights Reserved.
  // See "LICENSE" for details.

  // Extended JavaScript BN functions, required for RSA private ops.

  // Version 1.1: new BigInteger("0", 10) returns "proper" zero
  // Version 1.2: square() API, isProbablePrime fix

  // (public)
  function bnClone() { var r = nbi(); this.copyTo(r); return r; }

  // (public) return value as integer
  function bnIntValue() {
    if (this.s < 0) {
      if (this.t == 1) return this[0] - this.DV;
      else if (this.t == 0) return -1;
    }
    else if (this.t == 1) return this[0];
    else if (this.t == 0) return 0;
    // assumes 16 < DB < 32
    return ((this[1] & ((1 << (32 - this.DB)) - 1)) << this.DB) | this[0];
  }

  // (public) return value as byte
  function bnByteValue() { return (this.t == 0) ? this.s : (this[0] << 24) >> 24; }

  // (public) return value as short (assumes DB>=16)
  function bnShortValue() { return (this.t == 0) ? this.s : (this[0] << 16) >> 16; }

  // (protected) return x s.t. r^x < DV
  function bnpChunkSize(r) { return Math.floor(Math.LN2 * this.DB / Math.log(r)); }

  // (public) 0 if this == 0, 1 if this > 0
  function bnSigNum() {
    if (this.s < 0) return -1;
    else if (this.t <= 0 || (this.t == 1 && this[0] <= 0)) return 0;
    else return 1;
  }

  // (protected) convert to radix string
  function bnpToRadix(b) {
    if (b == null) b = 10;
    if (this.signum() == 0 || b < 2 || b > 36) return "0";
    var cs = this.chunkSize(b);
    var a = Math.pow(b, cs);
    var d = nbv(a), y = nbi(), z = nbi(), r = "";
    this.divRemTo(d, y, z);
    while (y.signum() > 0) {
      r = (a + z.intValue()).toString(b).substr(1) + r;
      y.divRemTo(d, y, z);
    }
    return z.intValue().toString(b) + r;
  }

  // (protected) convert from radix string
  function bnpFromRadix(s, b) {
    this.fromInt(0);
    if (b == null) b = 10;
    var cs = this.chunkSize(b);
    var d = Math.pow(b, cs), mi = false, j = 0, w = 0;
    for (var i = 0; i < s.length; ++i) {
      var x = intAt(s, i);
      if (x < 0) {
        if (s.charAt(i) == "-" && this.signum() == 0) mi = true;
        continue;
      }
      w = b * w + x;
      if (++j >= cs) {
        this.dMultiply(d);
        this.dAddOffset(w, 0);
        j = 0;
        w = 0;
      }
    }
    if (j > 0) {
      this.dMultiply(Math.pow(b, j));
      this.dAddOffset(w, 0);
    }
    if (mi) BigInteger.ZERO.subTo(this, this);
  }

  // (protected) alternate constructor
  function bnpFromNumber(a, b, c) {
    if ("number" == typeof b) {
      // new BigInteger(int,int,RNG)
      if (a < 2) this.fromInt(1);
      else {
        this.fromNumber(a, c);
        if (!this.testBit(a - 1))    // force MSB set
          this.bitwiseTo(BigInteger.ONE.shiftLeft(a - 1), op_or, this);
        if (this.isEven()) this.dAddOffset(1, 0); // force odd
        while (!this.isProbablePrime(b)) {
          this.dAddOffset(2, 0);
          if (this.bitLength() > a) this.subTo(BigInteger.ONE.shiftLeft(a - 1), this);
        }
      }
    }
    else {
      // new BigInteger(int,RNG)
      var x = new Array(), t = a & 7;
      x.length = (a >> 3) + 1;
      b.nextBytes(x);
      if (t > 0) x[0] &= ((1 << t) - 1); else x[0] = 0;
      this.fromString(x, 256);
    }
  }

  // (public) convert to bigendian byte array
  function bnToByteArray() {
    var i = this.t, r = new Array();
    r[0] = this.s;
    var p = this.DB - (i * this.DB) % 8, d, k = 0;
    if (i-- > 0) {
      if (p < this.DB && (d = this[i] >> p) != (this.s & this.DM) >> p)
        r[k++] = d | (this.s << (this.DB - p));
      while (i >= 0) {
        if (p < 8) {
          d = (this[i] & ((1 << p) - 1)) << (8 - p);
          d |= this[--i] >> (p += this.DB - 8);
        }
        else {
          d = (this[i] >> (p -= 8)) & 0xff;
          if (p <= 0) { p += this.DB; --i; }
        }
        if ((d & 0x80) != 0) d |= -256;
        if (k == 0 && (this.s & 0x80) != (d & 0x80))++k;
        if (k > 0 || d != this.s) r[k++] = d;
      }
    }
    return r;
  }

  function bnEquals(a) { return (this.compareTo(a) == 0); }
  function bnMin(a) { return (this.compareTo(a) < 0) ? this : a; }
  function bnMax(a) { return (this.compareTo(a) > 0) ? this : a; }

  // (protected) r = this op a (bitwise)
  function bnpBitwiseTo(a, op, r) {
    var i, f, m = Math.min(a.t, this.t);
    for (i = 0; i < m; ++i) r[i] = op(this[i], a[i]);
    if (a.t < this.t) {
      f = a.s & this.DM;
      for (i = m; i < this.t; ++i) r[i] = op(this[i], f);
      r.t = this.t;
    }
    else {
      f = this.s & this.DM;
      for (i = m; i < a.t; ++i) r[i] = op(f, a[i]);
      r.t = a.t;
    }
    r.s = op(this.s, a.s);
    r.clamp();
  }

  // (public) this & a
  function op_and(x, y) { return x & y; }
  function bnAnd(a) { var r = nbi(); this.bitwiseTo(a, op_and, r); return r; }

  // (public) this | a
  function op_or(x, y) { return x | y; }
  function bnOr(a) { var r = nbi(); this.bitwiseTo(a, op_or, r); return r; }

  // (public) this ^ a
  function op_xor(x, y) { return x ^ y; }
  function bnXor(a) { var r = nbi(); this.bitwiseTo(a, op_xor, r); return r; }

  // (public) this & ~a
  function op_andnot(x, y) { return x & ~y; }
  function bnAndNot(a) { var r = nbi(); this.bitwiseTo(a, op_andnot, r); return r; }

  // (public) ~this
  function bnNot() {
    var r = nbi();
    for (var i = 0; i < this.t; ++i) r[i] = this.DM & ~this[i];
    r.t = this.t;
    r.s = ~this.s;
    return r;
  }

  // (public) this << n
  function bnShiftLeft(n) {
    var r = nbi();
    if (n < 0) this.rShiftTo(-n, r); else this.lShiftTo(n, r);
    return r;
  }

  // (public) this >> n
  function bnShiftRight(n) {
    var r = nbi();
    if (n < 0) this.lShiftTo(-n, r); else this.rShiftTo(n, r);
    return r;
  }

  // return index of lowest 1-bit in x, x < 2^31
  function lbit(x) {
    if (x == 0) return -1;
    var r = 0;
    if ((x & 0xffff) == 0) { x >>= 16; r += 16; }
    if ((x & 0xff) == 0) { x >>= 8; r += 8; }
    if ((x & 0xf) == 0) { x >>= 4; r += 4; }
    if ((x & 3) == 0) { x >>= 2; r += 2; }
    if ((x & 1) == 0)++r;
    return r;
  }

  // (public) returns index of lowest 1-bit (or -1 if none)
  function bnGetLowestSetBit() {
    for (var i = 0; i < this.t; ++i)
      if (this[i] != 0) return i * this.DB + lbit(this[i]);
    if (this.s < 0) return this.t * this.DB;
    return -1;
  }

  // return number of 1 bits in x
  function cbit(x) {
    var r = 0;
    while (x != 0) { x &= x - 1; ++r; }
    return r;
  }

  // (public) return number of set bits
  function bnBitCount() {
    var r = 0, x = this.s & this.DM;
    for (var i = 0; i < this.t; ++i) r += cbit(this[i] ^ x);
    return r;
  }

  // (public) true iff nth bit is set
  function bnTestBit(n) {
    var j = Math.floor(n / this.DB);
    if (j >= this.t) return (this.s != 0);
    return ((this[j] & (1 << (n % this.DB))) != 0);
  }

  // (protected) this op (1<<n)
  function bnpChangeBit(n, op) {
    var r = BigInteger.ONE.shiftLeft(n);
    this.bitwiseTo(r, op, r);
    return r;
  }

  // (public) this | (1<<n)
  function bnSetBit(n) { return this.changeBit(n, op_or); }

  // (public) this & ~(1<<n)
  function bnClearBit(n) { return this.changeBit(n, op_andnot); }

  // (public) this ^ (1<<n)
  function bnFlipBit(n) { return this.changeBit(n, op_xor); }

  // (protected) r = this + a
  function bnpAddTo(a, r) {
    var i = 0, c = 0, m = Math.min(a.t, this.t);
    while (i < m) {
      c += this[i] + a[i];
      r[i++] = c & this.DM;
      c >>= this.DB;
    }
    if (a.t < this.t) {
      c += a.s;
      while (i < this.t) {
        c += this[i];
        r[i++] = c & this.DM;
        c >>= this.DB;
      }
      c += this.s;
    }
    else {
      c += this.s;
      while (i < a.t) {
        c += a[i];
        r[i++] = c & this.DM;
        c >>= this.DB;
      }
      c += a.s;
    }
    r.s = (c < 0) ? -1 : 0;
    if (c > 0) r[i++] = c;
    else if (c < -1) r[i++] = this.DV + c;
    r.t = i;
    r.clamp();
  }

  // (public) this + a
  function bnAdd(a) { var r = nbi(); this.addTo(a, r); return r; }

  // (public) this - a
  function bnSubtract(a) { var r = nbi(); this.subTo(a, r); return r; }

  // (public) this * a
  function bnMultiply(a) { var r = nbi(); this.multiplyTo(a, r); return r; }

  // (public) this^2
  function bnSquare() { var r = nbi(); this.squareTo(r); return r; }

  // (public) this / a
  function bnDivide(a) { var r = nbi(); this.divRemTo(a, r, null); return r; }

  // (public) this % a
  function bnRemainder(a) { var r = nbi(); this.divRemTo(a, null, r); return r; }

  // (public) [this/a,this%a]
  function bnDivideAndRemainder(a) {
    var q = nbi(), r = nbi();
    this.divRemTo(a, q, r);
    return new Array(q, r);
  }

  // (protected) this *= n, this >= 0, 1 < n < DV
  function bnpDMultiply(n) {
    this[this.t] = this.am(0, n - 1, this, 0, 0, this.t);
    ++this.t;
    this.clamp();
  }

  // (protected) this += n << w words, this >= 0
  function bnpDAddOffset(n, w) {
    if (n == 0) return;
    while (this.t <= w) this[this.t++] = 0;
    this[w] += n;
    while (this[w] >= this.DV) {
      this[w] -= this.DV;
      if (++w >= this.t) this[this.t++] = 0;
      ++this[w];
    }
  }

  // A "null" reducer
  function NullExp() { }
  function nNop(x) { return x; }
  function nMulTo(x, y, r) { x.multiplyTo(y, r); }
  function nSqrTo(x, r) { x.squareTo(r); }

  NullExp.prototype.convert = nNop;
  NullExp.prototype.revert = nNop;
  NullExp.prototype.mulTo = nMulTo;
  NullExp.prototype.sqrTo = nSqrTo;

  // (public) this^e
  function bnPow(e) { return this.exp(e, new NullExp()); }

  // (protected) r = lower n words of "this * a", a.t <= n
  // "this" should be the larger one if appropriate.
  function bnpMultiplyLowerTo(a, n, r) {
    var i = Math.min(this.t + a.t, n);
    r.s = 0; // assumes a,this >= 0
    r.t = i;
    while (i > 0) r[--i] = 0;
    var j;
    for (j = r.t - this.t; i < j; ++i) r[i + this.t] = this.am(0, a[i], r, i, 0, this.t);
    for (j = Math.min(a.t, n); i < j; ++i) this.am(0, a[i], r, i, 0, n - i);
    r.clamp();
  }

  // (protected) r = "this * a" without lower n words, n > 0
  // "this" should be the larger one if appropriate.
  function bnpMultiplyUpperTo(a, n, r) {
    --n;
    var i = r.t = this.t + a.t - n;
    r.s = 0; // assumes a,this >= 0
    while (--i >= 0) r[i] = 0;
    for (i = Math.max(n - this.t, 0); i < a.t; ++i)
      r[this.t + i - n] = this.am(n - i, a[i], r, 0, 0, this.t + i - n);
    r.clamp();
    r.drShiftTo(1, r);
  }

  // Barrett modular reduction
  function Barrett(m) {
    // setup Barrett
    this.r2 = nbi();
    this.q3 = nbi();
    BigInteger.ONE.dlShiftTo(2 * m.t, this.r2);
    this.mu = this.r2.divide(m);
    this.m = m;
  }

  function barrettConvert(x) {
    if (x.s < 0 || x.t > 2 * this.m.t) return x.mod(this.m);
    else if (x.compareTo(this.m) < 0) return x;
    else { var r = nbi(); x.copyTo(r); this.reduce(r); return r; }
  }

  function barrettRevert(x) { return x; }

  // x = x mod m (HAC 14.42)
  function barrettReduce(x) {
    x.drShiftTo(this.m.t - 1, this.r2);
    if (x.t > this.m.t + 1) { x.t = this.m.t + 1; x.clamp(); }
    this.mu.multiplyUpperTo(this.r2, this.m.t + 1, this.q3);
    this.m.multiplyLowerTo(this.q3, this.m.t + 1, this.r2);
    while (x.compareTo(this.r2) < 0) x.dAddOffset(1, this.m.t + 1);
    x.subTo(this.r2, x);
    while (x.compareTo(this.m) >= 0) x.subTo(this.m, x);
  }

  // r = x^2 mod m; x != r
  function barrettSqrTo(x, r) { x.squareTo(r); this.reduce(r); }

  // r = x*y mod m; x,y != r
  function barrettMulTo(x, y, r) { x.multiplyTo(y, r); this.reduce(r); }

  Barrett.prototype.convert = barrettConvert;
  Barrett.prototype.revert = barrettRevert;
  Barrett.prototype.reduce = barrettReduce;
  Barrett.prototype.mulTo = barrettMulTo;
  Barrett.prototype.sqrTo = barrettSqrTo;

  // (public) this^e % m (HAC 14.85)
  function bnModPow(e, m) {
    var i = e.bitLength(), k, r = nbv(1), z;
    if (i <= 0) return r;
    else if (i < 18) k = 1;
    else if (i < 48) k = 3;
    else if (i < 144) k = 4;
    else if (i < 768) k = 5;
    else k = 6;
    if (i < 8)
      z = new Classic(m);
    else if (m.isEven())
      z = new Barrett(m);
    else
      z = new Montgomery(m);

    // precomputation
    var g = new Array(), n = 3, k1 = k - 1, km = (1 << k) - 1;
    g[1] = z.convert(this);
    if (k > 1) {
      var g2 = nbi();
      z.sqrTo(g[1], g2);
      while (n <= km) {
        g[n] = nbi();
        z.mulTo(g2, g[n - 2], g[n]);
        n += 2;
      }
    }

    var j = e.t - 1, w, is1 = true, r2 = nbi(), t;
    i = nbits(e[j]) - 1;
    while (j >= 0) {
      if (i >= k1) w = (e[j] >> (i - k1)) & km;
      else {
        w = (e[j] & ((1 << (i + 1)) - 1)) << (k1 - i);
        if (j > 0) w |= e[j - 1] >> (this.DB + i - k1);
      }

      n = k;
      while ((w & 1) == 0) { w >>= 1; --n; }
      if ((i -= n) < 0) { i += this.DB; --j; }
      if (is1) {    // ret == 1, don't bother squaring or multiplying it
        g[w].copyTo(r);
        is1 = false;
      }
      else {
        while (n > 1) { z.sqrTo(r, r2); z.sqrTo(r2, r); n -= 2; }
        if (n > 0) z.sqrTo(r, r2); else { t = r; r = r2; r2 = t; }
        z.mulTo(r2, g[w], r);
      }

      while (j >= 0 && (e[j] & (1 << i)) == 0) {
        z.sqrTo(r, r2); t = r; r = r2; r2 = t;
        if (--i < 0) { i = this.DB - 1; --j; }
      }
    }
    return z.revert(r);
  }

  // (public) gcd(this,a) (HAC 14.54)
  function bnGCD(a) {
    var x = (this.s < 0) ? this.negate() : this.clone();
    var y = (a.s < 0) ? a.negate() : a.clone();
    if (x.compareTo(y) < 0) { var t = x; x = y; y = t; }
    var i = x.getLowestSetBit(), g = y.getLowestSetBit();
    if (g < 0) return x;
    if (i < g) g = i;
    if (g > 0) {
      x.rShiftTo(g, x);
      y.rShiftTo(g, y);
    }
    while (x.signum() > 0) {
      if ((i = x.getLowestSetBit()) > 0) x.rShiftTo(i, x);
      if ((i = y.getLowestSetBit()) > 0) y.rShiftTo(i, y);
      if (x.compareTo(y) >= 0) {
        x.subTo(y, x);
        x.rShiftTo(1, x);
      }
      else {
        y.subTo(x, y);
        y.rShiftTo(1, y);
      }
    }
    if (g > 0) y.lShiftTo(g, y);
    return y;
  }

  // (protected) this % n, n < 2^26
  function bnpModInt(n) {
    if (n <= 0) return 0;
    var d = this.DV % n, r = (this.s < 0) ? n - 1 : 0;
    if (this.t > 0)
      if (d == 0) r = this[0] % n;
      else for (var i = this.t - 1; i >= 0; --i) r = (d * r + this[i]) % n;
    return r;
  }

  // (public) 1/this % m (HAC 14.61)
  function bnModInverse(m) {
    var ac = m.isEven();
    if ((this.isEven() && ac) || m.signum() == 0) return BigInteger.ZERO;
    var u = m.clone(), v = this.clone();
    var a = nbv(1), b = nbv(0), c = nbv(0), d = nbv(1);
    while (u.signum() != 0) {
      while (u.isEven()) {
        u.rShiftTo(1, u);
        if (ac) {
          if (!a.isEven() || !b.isEven()) { a.addTo(this, a); b.subTo(m, b); }
          a.rShiftTo(1, a);
        }
        else if (!b.isEven()) b.subTo(m, b);
        b.rShiftTo(1, b);
      }
      while (v.isEven()) {
        v.rShiftTo(1, v);
        if (ac) {
          if (!c.isEven() || !d.isEven()) { c.addTo(this, c); d.subTo(m, d); }
          c.rShiftTo(1, c);
        }
        else if (!d.isEven()) d.subTo(m, d);
        d.rShiftTo(1, d);
      }
      if (u.compareTo(v) >= 0) {
        u.subTo(v, u);
        if (ac) a.subTo(c, a);
        b.subTo(d, b);
      }
      else {
        v.subTo(u, v);
        if (ac) c.subTo(a, c);
        d.subTo(b, d);
      }
    }
    if (v.compareTo(BigInteger.ONE) != 0) return BigInteger.ZERO;
    if (d.compareTo(m) >= 0) return d.subtract(m);
    if (d.signum() < 0) d.addTo(m, d); else return d;
    if (d.signum() < 0) return d.add(m); else return d;
  }

  var lowprimes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997];
  var lplim = (1 << 26) / lowprimes[lowprimes.length - 1];

  // (public) test primality with certainty >= 1-.5^t
  function bnIsProbablePrime(t) {
    var i, x = this.abs();
    if (x.t == 1 && x[0] <= lowprimes[lowprimes.length - 1]) {
      for (i = 0; i < lowprimes.length; ++i)
        if (x[0] == lowprimes[i]) return true;
      return false;
    }
    if (x.isEven()) return false;
    i = 1;
    while (i < lowprimes.length) {
      var m = lowprimes[i], j = i + 1;
      while (j < lowprimes.length && m < lplim) m *= lowprimes[j++];
      m = x.modInt(m);
      while (i < j) if (m % lowprimes[i++] == 0) return false;
    }
    return x.millerRabin(t);
  }

  // (protected) true if probably prime (HAC 4.24, Miller-Rabin)
  function bnpMillerRabin(t) {
    var n1 = this.subtract(BigInteger.ONE);
    var k = n1.getLowestSetBit();
    if (k <= 0) return false;
    var r = n1.shiftRight(k);
    t = (t + 1) >> 1;
    if (t > lowprimes.length) t = lowprimes.length;
    var a = nbi();
    for (var i = 0; i < t; ++i) {
      //Pick bases at random, instead of starting at 2
      a.fromInt(lowprimes[Math.floor(Math.random() * lowprimes.length)]);
      var y = a.modPow(r, this);
      if (y.compareTo(BigInteger.ONE) != 0 && y.compareTo(n1) != 0) {
        var j = 1;
        while (j++ < k && y.compareTo(n1) != 0) {
          y = y.modPowInt(2, this);
          if (y.compareTo(BigInteger.ONE) == 0) return false;
        }
        if (y.compareTo(n1) != 0) return false;
      }
    }
    return true;
  }

  // protected
  BigInteger.prototype.chunkSize = bnpChunkSize;
  BigInteger.prototype.toRadix = bnpToRadix;
  BigInteger.prototype.fromRadix = bnpFromRadix;
  BigInteger.prototype.fromNumber = bnpFromNumber;
  BigInteger.prototype.bitwiseTo = bnpBitwiseTo;
  BigInteger.prototype.changeBit = bnpChangeBit;
  BigInteger.prototype.addTo = bnpAddTo;
  BigInteger.prototype.dMultiply = bnpDMultiply;
  BigInteger.prototype.dAddOffset = bnpDAddOffset;
  BigInteger.prototype.multiplyLowerTo = bnpMultiplyLowerTo;
  BigInteger.prototype.multiplyUpperTo = bnpMultiplyUpperTo;
  BigInteger.prototype.modInt = bnpModInt;
  BigInteger.prototype.millerRabin = bnpMillerRabin;

  // public
  BigInteger.prototype.clone = bnClone;
  BigInteger.prototype.intValue = bnIntValue;
  BigInteger.prototype.byteValue = bnByteValue;
  BigInteger.prototype.shortValue = bnShortValue;
  BigInteger.prototype.signum = bnSigNum;
  BigInteger.prototype.toByteArray = bnToByteArray;
  BigInteger.prototype.equals = bnEquals;
  BigInteger.prototype.min = bnMin;
  BigInteger.prototype.max = bnMax;
  BigInteger.prototype.and = bnAnd;
  BigInteger.prototype.or = bnOr;
  BigInteger.prototype.xor = bnXor;
  BigInteger.prototype.andNot = bnAndNot;
  BigInteger.prototype.not = bnNot;
  BigInteger.prototype.shiftLeft = bnShiftLeft;
  BigInteger.prototype.shiftRight = bnShiftRight;
  BigInteger.prototype.getLowestSetBit = bnGetLowestSetBit;
  BigInteger.prototype.bitCount = bnBitCount;
  BigInteger.prototype.testBit = bnTestBit;
  BigInteger.prototype.setBit = bnSetBit;
  BigInteger.prototype.clearBit = bnClearBit;
  BigInteger.prototype.flipBit = bnFlipBit;
  BigInteger.prototype.add = bnAdd;
  BigInteger.prototype.subtract = bnSubtract;
  BigInteger.prototype.multiply = bnMultiply;
  BigInteger.prototype.divide = bnDivide;
  BigInteger.prototype.remainder = bnRemainder;
  BigInteger.prototype.divideAndRemainder = bnDivideAndRemainder;
  BigInteger.prototype.modPow = bnModPow;
  BigInteger.prototype.modInverse = bnModInverse;
  BigInteger.prototype.pow = bnPow;
  BigInteger.prototype.gcd = bnGCD;
  BigInteger.prototype.isProbablePrime = bnIsProbablePrime;

  // JSBN-specific extension
  BigInteger.prototype.square = bnSquare;

  // Expose the Barrett function
  BigInteger.prototype.Barrett = Barrett

  // BigInteger interfaces not implemented in jsbn:

  // BigInteger(int signum, byte[] magnitude)
  // double doubleValue()
  // float floatValue()
  // int hashCode()
  // long longValue()
  // static BigInteger valueOf(long val)

  // Random number generator - requires a PRNG backend, e.g. prng4.js

  // For best results, put code like
  // <body onClick='rng_seed_time();' onKeyPress='rng_seed_time();'>
  // in your main HTML document.

  var rng_state;
  var rng_pool;
  var rng_pptr;

  // Mix in a 32-bit integer into the pool
  function rng_seed_int(x) {
    rng_pool[rng_pptr++] ^= x & 255;
    rng_pool[rng_pptr++] ^= (x >> 8) & 255;
    rng_pool[rng_pptr++] ^= (x >> 16) & 255;
    rng_pool[rng_pptr++] ^= (x >> 24) & 255;
    if (rng_pptr >= rng_psize) rng_pptr -= rng_psize;
  }

  // Mix in the current time (w/milliseconds) into the pool
  function rng_seed_time() {
    rng_seed_int(new Date().getTime());
  }

  // Initialize the pool with junk if needed.
  if (rng_pool == null) {
    rng_pool = new Array();
    rng_pptr = 0;
    var t;
    if (typeof window !== "undefined" && window.crypto) {
      if (window.crypto.getRandomValues) {
        // Use webcrypto if available
        var ua = new Uint8Array(32);
        window.crypto.getRandomValues(ua);
        for (t = 0; t < 32; ++t)
          rng_pool[rng_pptr++] = ua[t];
      }
      else if (navigator.appName == "Netscape" && navigator.appVersion < "5") {
        // Extract entropy (256 bits) from NS4 RNG if available
        var z = window.crypto.random(32);
        for (t = 0; t < z.length; ++t)
          rng_pool[rng_pptr++] = z.charCodeAt(t) & 255;
      }
    }
    while (rng_pptr < rng_psize) {  // extract some randomness from Math.random()
      t = Math.floor(65536 * Math.random());
      rng_pool[rng_pptr++] = t >>> 8;
      rng_pool[rng_pptr++] = t & 255;
    }
    rng_pptr = 0;
    rng_seed_time();
    //rng_seed_int(window.screenX);
    //rng_seed_int(window.screenY);
  }

  function rng_get_byte() {
    if (rng_state == null) {
      rng_seed_time();
      rng_state = prng_newstate();
      rng_state.init(rng_pool);
      for (rng_pptr = 0; rng_pptr < rng_pool.length; ++rng_pptr)
        rng_pool[rng_pptr] = 0;
      rng_pptr = 0;
      //rng_pool = null;
    }
    // TODO: allow reseeding after first request
    return rng_state.next();
  }

  function rng_get_bytes(ba) {
    var i;
    for (i = 0; i < ba.length; ++i) ba[i] = rng_get_byte();
  }

  function SecureRandom() { }

  SecureRandom.prototype.nextBytes = rng_get_bytes;

  // prng4.js - uses Arcfour as a PRNG

  function Arcfour() {
    this.i = 0;
    this.j = 0;
    this.S = new Array();
  }

  // Initialize arcfour context from key, an array of ints, each from [0..255]
  function ARC4init(key) {
    var i, j, t;
    for (i = 0; i < 256; ++i)
      this.S[i] = i;
    j = 0;
    for (i = 0; i < 256; ++i) {
      j = (j + this.S[i] + key[i % key.length]) & 255;
      t = this.S[i];
      this.S[i] = this.S[j];
      this.S[j] = t;
    }
    this.i = 0;
    this.j = 0;
  }

  function ARC4next() {
    var t;
    this.i = (this.i + 1) & 255;
    this.j = (this.j + this.S[this.i]) & 255;
    t = this.S[this.i];
    this.S[this.i] = this.S[this.j];
    this.S[this.j] = t;
    return this.S[(t + this.S[this.i]) & 255];
  }

  Arcfour.prototype.init = ARC4init;
  Arcfour.prototype.next = ARC4next;

  // Plug in your RNG constructor here
  function prng_newstate() {
    return new Arcfour();
  }

  // Pool size must be a multiple of 4 and greater than 32.
  // An array of bytes the size of the pool will be passed to init()
  var rng_psize = 256;

  return {
    BigInteger: BigInteger,
    SecureRandom: SecureRandom
  };

}).call(this);



function $partial_0_1$prim_95__95_floatToStr(){
    return (function(x1){
        return prim_95__95_floatToStr(x1);
    });
}

function $partial_0_2$prim_95__95_strCons(){
    return (function(x1){
        return (function(x2){
            return prim_95__95_strCons(x1, x2);
        });
    });
}

function $partial_0_1$prim_95__95_toStrBigInt(){
    return (function(x1){
        return prim_95__95_toStrBigInt(x1);
    });
}

function $partial_5_10$TParsec__Combinators__alt(x1, x2, x3, x4, x5){
    return (function(x6){
        return (function(x7){
            return (function(x8){
                return (function(x9){
                    return (function(x10){
                        return TParsec__Combinators__alt(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10);
                    });
                });
            });
        });
    });
}

function $partial_7_10$TParsec__Combinators__alt(x1, x2, x3, x4, x5, x6, x7){
    return (function(x8){
        return (function(x9){
            return (function(x10){
                return TParsec__Combinators__alt(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10);
            });
        });
    });
}

function $partial_5_6$TParsec__Success__and(x1, x2, x3, x4, x5){
    return (function(x6){
        return TParsec__Success__and(x1, x2, x3, x4, x5, x6);
    });
}

function $partial_8_11$TParsec__Combinators__andbind(x1, x2, x3, x4, x5, x6, x7, x8){
    return (function(x9){
        return (function(x10){
            return (function(x11){
                return TParsec__Combinators__andbind(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11);
            });
        });
    });
}

function $partial_10_11$TParsec__Combinators__andbind(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10){
    return (function(x11){
        return TParsec__Combinators__andbind(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11);
    });
}

function $partial_8_11$TParsec__Combinators__andbindm(x1, x2, x3, x4, x5, x6, x7, x8){
    return (function(x9){
        return (function(x10){
            return (function(x11){
                return TParsec__Combinators__andbindm(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11);
            });
        });
    });
}

function $partial_9_12$TParsec__Combinators__andoptbind(x1, x2, x3, x4, x5, x6, x7, x8, x9){
    return (function(x10){
        return (function(x11){
            return (function(x12){
                return TParsec__Combinators__andoptbind(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12);
            });
        });
    });
}

function $partial_5_8$TParsec__Combinators__anyTok(x1, x2, x3, x4, x5){
    return (function(x6){
        return (function(x7){
            return (function(x8){
                return TParsec__Combinators__anyTok(x1, x2, x3, x4, x5, x6, x7, x8);
            });
        });
    });
}

function $partial_7_8$TParsec__Combinators__exact(x1, x2, x3, x4, x5, x6, x7){
    return (function(x8){
        return TParsec__Combinators__exact(x1, x2, x3, x4, x5, x6, x7, x8);
    });
}

function $partial_7_8$ParserUtils__except(x1, x2, x3, x4, x5, x6, x7){
    return (function(x8){
        return ParserUtils__except(x1, x2, x3, x4, x5, x6, x7, x8);
    });
}

function $partial_9_12$TParsec__Combinators__guardM(x1, x2, x3, x4, x5, x6, x7, x8, x9){
    return (function(x10){
        return (function(x11){
            return (function(x12){
                return TParsec__Combinators__guardM(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12);
            });
        });
    });
}

function $partial_0_1$Backend__Haskell__guardParen(){
    return (function(x1){
        return Backend__Haskell__guardParen(x1);
    });
}

function $partial_1_2$Backend__Haskell__makeDefs(x1){
    return (function(x2){
        return Backend__Haskell__makeDefs(x1, x2);
    });
}

function $partial_0_1$Backend__JSON__makeDefs(){
    return (function(x1){
        return Backend__JSON__makeDefs(x1);
    });
}

function $partial_1_2$Backend__ReasonML__makeDefs(x1){
    return (function(x2){
        return Backend__ReasonML__makeDefs(x1, x2);
    });
}

function $partial_0_1$Typedefs__makeName(){
    return (function(x1){
        return Typedefs__makeName(x1);
    });
}

function $partial_0_1$Backend__JSON__makeSubSchema(){
    return (function(x1){
        return Backend__JSON__makeSubSchema(x1);
    });
}

function $partial_2_3$Backend__Haskell__makeType(x1, x2){
    return (function(x3){
        return Backend__Haskell__makeType(x1, x2, x3);
    });
}

function $partial_2_3$Backend__ReasonML__makeType(x1, x2){
    return (function(x3){
        return Backend__ReasonML__makeType(x1, x2, x3);
    });
}

function $partial_8_11$TParsec__Combinators__mand(x1, x2, x3, x4, x5, x6, x7, x8){
    return (function(x9){
        return (function(x10){
            return (function(x11){
                return TParsec__Combinators__mand(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11);
            });
        });
    });
}

function $partial_7_11$TParsec__Combinators__map(x1, x2, x3, x4, x5, x6, x7){
    return (function(x8){
        return (function(x9){
            return (function(x10){
                return (function(x11){
                    return TParsec__Combinators__map(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11);
                });
            });
        });
    });
}

function $partial_8_11$TParsec__Combinators__map(x1, x2, x3, x4, x5, x6, x7, x8){
    return (function(x9){
        return (function(x10){
            return (function(x11){
                return TParsec__Combinators__map(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11);
            });
        });
    });
}

function $partial_10_11$TParsec__Combinators__map(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10){
    return (function(x11){
        return TParsec__Combinators__map(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11);
    });
}

function $partial_0_1$Parse__parseTNamed(){
    return (function(x1){
        return Parse__parseTNamed(x1);
    });
}

function $partial_0_1$Backend__Haskell__renderDef(){
    return (function(x1){
        return Backend__Haskell__renderDef(x1);
    });
}

function $partial_0_1$Backend__ReasonML__renderDef(){
    return (function(x1){
        return Backend__ReasonML__renderDef(x1);
    });
}

function $partial_0_1$Backend__Haskell__renderType(){
    return (function(x1){
        return Backend__Haskell__renderType(x1);
    });
}

function $partial_0_1$Backend__ReasonML__renderType(){
    return (function(x1){
        return Backend__ReasonML__renderType(x1);
    });
}

function $partial_1_2$Typedefs__shiftVars(x1){
    return (function(x2){
        return Typedefs__shiftVars(x1, x2);
    });
}

function $partial_0_1$Text__PrettyPrint__WL__Core__text(){
    return (function(x1){
        return Text__PrettyPrint__WL__Core__text(x1);
    });
}

function $partial_0_1$Parse__tnamedRec(){
    return (function(x1){
        return Parse__tnamedRec(x1);
    });
}

function $partial_1_2$TParsec__Combinators__Chars___123_alphas_95_0_125_(x1){
    return (function(x2){
        return TParsec__Combinators__Chars___123_alphas_95_0_125_(x1, x2);
    });
}

function $partial_1_4$TParsec__Combinators___123_alts_95_1_125_(x1){
    return (function(x2){
        return (function(x3){
            return (function(x4){
                return TParsec__Combinators___123_alts_95_1_125_(x1, x2, x3, x4);
            });
        });
    });
}

function $partial_2_3$TParsec__Combinators___123_andbind_95_2_125_(x1, x2){
    return (function(x3){
        return TParsec__Combinators___123_andbind_95_2_125_(x1, x2, x3);
    });
}

function $partial_2_3$TParsec__Combinators___123_andbindm_95_3_125_(x1, x2){
    return (function(x3){
        return TParsec__Combinators___123_andbindm_95_3_125_(x1, x2, x3);
    });
}

function $partial_2_3$TParsec__Combinators___123_andbindm_95_4_125_(x1, x2){
    return (function(x3){
        return TParsec__Combinators___123_andbindm_95_4_125_(x1, x2, x3);
    });
}

function $partial_1_2$TParsec__Combinators___123_andoptbind_95_5_125_(x1){
    return (function(x2){
        return TParsec__Combinators___123_andoptbind_95_5_125_(x1, x2);
    });
}

function $partial_3_4$TParsec__Combinators___123_andoptbind_95_6_125_(x1, x2, x3){
    return (function(x4){
        return TParsec__Combinators___123_andoptbind_95_6_125_(x1, x2, x3, x4);
    });
}

function $partial_0_1$TParsec__Combinators___123_ands_95_7_125_(){
    return (function(x1){
        return TParsec__Combinators___123_ands_95_7_125_(x1);
    });
}

function $partial_1_6$TParsec__Combinators___123_ands_95_8_125_(x1){
    return (function(x2){
        return (function(x3){
            return (function(x4){
                return (function(x5){
                    return (function(x6){
                        return TParsec__Combinators___123_ands_95_8_125_(x1, x2, x3, x4, x5, x6);
                    });
                });
            });
        });
    });
}

function $partial_1_3$TParsec__Combinators___123_ands_95_9_125_(x1){
    return (function(x2){
        return (function(x3){
            return TParsec__Combinators___123_ands_95_9_125_(x1, x2, x3);
        });
    });
}

function $partial_0_1$TParsec__Combinators___123_ands_95_10_125_(){
    return (function(x1){
        return TParsec__Combinators___123_ands_95_10_125_(x1);
    });
}

function $partial_5_6$TParsec__Combinators___123_anyOf_95_12_125_(x1, x2, x3, x4, x5){
    return (function(x6){
        return TParsec__Combinators___123_anyOf_95_12_125_(x1, x2, x3, x4, x5, x6);
    });
}

function $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(){
    return (function(x1){
        return (function(x2){
            return TParsec__Combinators___123_anyTok_95_13_125_(x1, x2);
        });
    });
}

function $partial_2_4$TParsec__Combinators___123_anyTok_95_14_125_(x1, x2){
    return (function(x3){
        return (function(x4){
            return TParsec__Combinators___123_anyTok_95_14_125_(x1, x2, x3, x4);
        });
    });
}

function $partial_2_3$Typedefs___123_ap_95_15_125_(x1, x2){
    return (function(x3){
        return Typedefs___123_ap_95_15_125_(x1, x2, x3);
    });
}

function $partial_2_3$Typedefs___123_ap_95_16_125_(x1, x2){
    return (function(x3){
        return Typedefs___123_ap_95_16_125_(x1, x2, x3);
    });
}

function $partial_0_2$Typedefs___123_apN_95_19_125_(){
    return (function(x1){
        return (function(x2){
            return Typedefs___123_apN_95_19_125_(x1, x2);
        });
    });
}

function $partial_0_1$Typedefs___123_apN_95_20_125_(){
    return (function(x1){
        return Typedefs___123_apN_95_20_125_(x1);
    });
}

function $partial_0_2$Prelude__Bits___123_b16ToHexString_95_23_125_(){
    return (function(x1){
        return (function(x2){
            return Prelude__Bits___123_b16ToHexString_95_23_125_(x1, x2);
        });
    });
}

function $partial_0_1$Data__NEList___123_consopt_95_24_125_(){
    return (function(x1){
        return Data__NEList___123_consopt_95_24_125_(x1);
    });
}

function $partial_1_2$TParsec__Combinators__Numbers___123_decimalDigit_95_25_125_(x1){
    return (function(x2){
        return TParsec__Combinators__Numbers___123_decimalDigit_95_25_125_(x1, x2);
    });
}

function $partial_6_7$TParsec__Combinators__Numbers___123_decimalDigit_95_26_125_(x1, x2, x3, x4, x5, x6){
    return (function(x7){
        return TParsec__Combinators__Numbers___123_decimalDigit_95_26_125_(x1, x2, x3, x4, x5, x6, x7);
    });
}

function $partial_0_2$TParsec__Combinators__Numbers___123_decimalNat_95_27_125_(){
    return (function(x1){
        return (function(x2){
            return TParsec__Combinators__Numbers___123_decimalNat_95_27_125_(x1, x2);
        });
    });
}

function $partial_0_1$TParsec__Combinators__Numbers___123_decimalNat_95_28_125_(){
    return (function(x1){
        return TParsec__Combinators__Numbers___123_decimalNat_95_28_125_(x1);
    });
}

function $partial_0_2$Backend__JSON___123_disjointSubSchema_95_29_125_(){
    return (function(x1){
        return (function(x2){
            return Backend__JSON___123_disjointSubSchema_95_29_125_(x1, x2);
        });
    });
}

function $partial_0_1$Parse___123_emptyComments_95_33_125_(){
    return (function(x1){
        return Parse___123_emptyComments_95_33_125_(x1);
    });
}

function $partial_1_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_34_125_(x1){
    return (function(x2){
        return Text__PrettyPrint__WL__Combinators___123_encloseSep_95_34_125_(x1, x2);
    });
}

function $partial_0_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_36_125_(){
    return (function(x1){
        return (function(x2){
            return Text__PrettyPrint__WL__Combinators___123_encloseSep_95_36_125_(x1, x2);
        });
    });
}

function $partial_0_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_37_125_(){
    return (function(x1){
        return (function(x2){
            return Text__PrettyPrint__WL__Combinators___123_encloseSep_95_37_125_(x1, x2);
        });
    });
}

function $partial_5_6$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_43_125_(x1, x2, x3, x4, x5){
    return (function(x6){
        return Text__PrettyPrint__WL__Combinators___123_encloseSep_95_43_125_(x1, x2, x3, x4, x5, x6);
    });
}

function $partial_4_5$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_44_125_(x1, x2, x3, x4){
    return (function(x5){
        return Text__PrettyPrint__WL__Combinators___123_encloseSep_95_44_125_(x1, x2, x3, x4, x5);
    });
}

function $partial_5_6$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_54_125_(x1, x2, x3, x4, x5){
    return (function(x6){
        return Text__PrettyPrint__WL__Combinators___123_encloseSep_95_54_125_(x1, x2, x3, x4, x5, x6);
    });
}

function $partial_4_5$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_55_125_(x1, x2, x3, x4){
    return (function(x5){
        return Text__PrettyPrint__WL__Combinators___123_encloseSep_95_55_125_(x1, x2, x3, x4, x5);
    });
}

function $partial_2_3$TParsec__Combinators___123_exact_95_57_125_(x1, x2){
    return (function(x3){
        return TParsec__Combinators___123_exact_95_57_125_(x1, x2, x3);
    });
}

function $partial_2_3$ParserUtils___123_except_95_59_125_(x1, x2){
    return (function(x3){
        return ParserUtils___123_except_95_59_125_(x1, x2, x3);
    });
}

function $partial_3_4$Data__Vect___123_foldrImpl_95_62_125_(x1, x2, x3){
    return (function(x4){
        return Data__Vect___123_foldrImpl_95_62_125_(x1, x2, x3, x4);
    });
}

function $partial_1_2$Backend__Utils___123_freshEnv_95_63_125_(x1){
    return (function(x2){
        return Backend__Utils___123_freshEnv_95_63_125_(x1, x2);
    });
}

function $partial_1_2$Main___123_generateCode_95_64_125_(x1){
    return (function(x2){
        return Main___123_generateCode_95_64_125_(x1, x2);
    });
}

function $partial_1_2$Main___123_generateCode_95_65_125_(x1){
    return (function(x2){
        return Main___123_generateCode_95_65_125_(x1, x2);
    });
}

function $partial_0_2$Backend___123_generateDefs_95_66_125_(){
    return (function(x1){
        return (function(x2){
            return Backend___123_generateDefs_95_66_125_(x1, x2);
        });
    });
}

function $partial_1_2$TParsec__Success___123_getTok_95_67_125_(x1){
    return (function(x2){
        return TParsec__Success___123_getTok_95_67_125_(x1, x2);
    });
}

function $partial_1_3$Typedefs___123_getUsedIndices_95_68_125_(x1){
    return (function(x2){
        return (function(x3){
            return Typedefs___123_getUsedIndices_95_68_125_(x1, x2, x3);
        });
    });
}

function $partial_1_3$Typedefs___123_getUsedIndices_95_69_125_(x1){
    return (function(x2){
        return (function(x3){
            return Typedefs___123_getUsedIndices_95_69_125_(x1, x2, x3);
        });
    });
}

function $partial_1_2$Typedefs___123_getUsedIndices_95_70_125_(x1){
    return (function(x2){
        return Typedefs___123_getUsedIndices_95_70_125_(x1, x2);
    });
}

function $partial_0_2$Typedefs___123_getUsedIndices_95_72_125_(){
    return (function(x1){
        return (function(x2){
            return Typedefs___123_getUsedIndices_95_72_125_(x1, x2);
        });
    });
}

function $partial_1_3$Typedefs___123_getUsedIndices_95_73_125_(x1){
    return (function(x2){
        return (function(x3){
            return Typedefs___123_getUsedIndices_95_73_125_(x1, x2, x3);
        });
    });
}

function $partial_2_4$TParsec__Combinators___123_guardM_95_82_125_(x1, x2){
    return (function(x3){
        return (function(x4){
            return TParsec__Combinators___123_guardM_95_82_125_(x1, x2, x3, x4);
        });
    });
}

function $partial_3_4$TParsec__Combinators___123_guardM_95_83_125_(x1, x2, x3){
    return (function(x4){
        return TParsec__Combinators___123_guardM_95_83_125_(x1, x2, x3, x4);
    });
}

function $partial_3_4$TParsec__Combinators___123_guardM_95_84_125_(x1, x2, x3){
    return (function(x4){
        return TParsec__Combinators___123_guardM_95_84_125_(x1, x2, x3, x4);
    });
}

function $partial_0_1$Backend__Haskell___123_hsParam_95_86_125_(){
    return (function(x1){
        return Backend__Haskell___123_hsParam_95_86_125_(x1);
    });
}

function $partial_0_1$Typedefs___123_idVars_95_87_125_(){
    return (function(x1){
        return Typedefs___123_idVars_95_87_125_(x1);
    });
}

function $partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return Backend__Utils___123_ifNotPresent_95_88_125_(x1, x2, x3);
            });
        });
    });
}

function $partial_0_4$Backend__Utils___123_ifNotPresent_95_91_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return (function(x4){
                    return Backend__Utils___123_ifNotPresent_95_91_125_(x1, x2, x3, x4);
                });
            });
        });
    });
}

function $partial_0_1$Backend__Utils___123_ifNotPresent_95_92_125_(){
    return (function(x1){
        return Backend__Utils___123_ifNotPresent_95_92_125_(x1);
    });
}

function $partial_1_3$Backend__Utils___123_ifNotPresent_95_104_125_(x1){
    return (function(x2){
        return (function(x3){
            return Backend__Utils___123_ifNotPresent_95_104_125_(x1, x2, x3);
        });
    });
}

function $partial_0_1$Backend__Utils___123_ifNotPresent_95_105_125_(){
    return (function(x1){
        return Backend__Utils___123_ifNotPresent_95_105_125_(x1);
    });
}

function $partial_3_4$Backend__Utils___123_ifNotPresent_95_106_125_(x1, x2, x3){
    return (function(x4){
        return Backend__Utils___123_ifNotPresent_95_106_125_(x1, x2, x3, x4);
    });
}

function $partial_7_11$Parse___123_ignorespaces_95_107_125_(x1, x2, x3, x4, x5, x6, x7){
    return (function(x8){
        return (function(x9){
            return (function(x10){
                return (function(x11){
                    return Parse___123_ignorespaces_95_107_125_(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11);
                });
            });
        });
    });
}

function $partial_0_1$TParsec__Combinators___123_land_95_108_125_(){
    return (function(x1){
        return TParsec__Combinators___123_land_95_108_125_(x1);
    });
}

function $partial_0_2$Backend__Haskell___123_makeDefs_95_123_125_(){
    return (function(x1){
        return (function(x2){
            return Backend__Haskell___123_makeDefs_95_123_125_(x1, x2);
        });
    });
}

function $partial_0_1$Backend__Haskell___123_makeDefs_95_125_125_(){
    return (function(x1){
        return Backend__Haskell___123_makeDefs_95_125_125_(x1);
    });
}

function $partial_0_4$Backend__Haskell___123_makeDefs_95_127_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return (function(x4){
                    return Backend__Haskell___123_makeDefs_95_127_125_(x1, x2, x3, x4);
                });
            });
        });
    });
}

function $partial_0_3$Backend__Haskell___123_makeDefs_95_128_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return Backend__Haskell___123_makeDefs_95_128_125_(x1, x2, x3);
            });
        });
    });
}

function $partial_0_4$Backend__Haskell___123_makeDefs_95_133_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return (function(x4){
                    return Backend__Haskell___123_makeDefs_95_133_125_(x1, x2, x3, x4);
                });
            });
        });
    });
}

function $partial_1_3$Backend__Haskell___123_makeDefs_95_134_125_(x1){
    return (function(x2){
        return (function(x3){
            return Backend__Haskell___123_makeDefs_95_134_125_(x1, x2, x3);
        });
    });
}

function $partial_2_3$Backend__Haskell___123_makeDefs_95_135_125_(x1, x2){
    return (function(x3){
        return Backend__Haskell___123_makeDefs_95_135_125_(x1, x2, x3);
    });
}

function $partial_0_2$Backend__JSON___123_makeDefs_95_161_125_(){
    return (function(x1){
        return (function(x2){
            return Backend__JSON___123_makeDefs_95_161_125_(x1, x2);
        });
    });
}

function $partial_0_2$Backend__JSON___123_makeDefs_95_162_125_(){
    return (function(x1){
        return (function(x2){
            return Backend__JSON___123_makeDefs_95_162_125_(x1, x2);
        });
    });
}

function $partial_0_1$Backend__JSON___123_makeDefs_95_163_125_(){
    return (function(x1){
        return Backend__JSON___123_makeDefs_95_163_125_(x1);
    });
}

function $partial_0_1$Backend__JSON___123_makeDefs_95_166_125_(){
    return (function(x1){
        return Backend__JSON___123_makeDefs_95_166_125_(x1);
    });
}

function $partial_2_3$Backend__ReasonML___123_makeDefs_95_213_125_(x1, x2){
    return (function(x3){
        return Backend__ReasonML___123_makeDefs_95_213_125_(x1, x2, x3);
    });
}

function $partial_1_2$Backend__ReasonML___123_makeDefs_95_243_125_(x1){
    return (function(x2){
        return Backend__ReasonML___123_makeDefs_95_243_125_(x1, x2);
    });
}

function $partial_0_1$Backend__ReasonML___123_makeDefs_95_244_125_(){
    return (function(x1){
        return Backend__ReasonML___123_makeDefs_95_244_125_(x1);
    });
}

function $partial_0_1$Backend__Haskell___123_makeDefs_39__95_248_125_(){
    return (function(x1){
        return Backend__Haskell___123_makeDefs_39__95_248_125_(x1);
    });
}

function $partial_0_1$Backend__Haskell___123_makeDefs_39__95_249_125_(){
    return (function(x1){
        return Backend__Haskell___123_makeDefs_39__95_249_125_(x1);
    });
}

function $partial_0_1$Backend__Haskell___123_makeDefs_39__95_250_125_(){
    return (function(x1){
        return Backend__Haskell___123_makeDefs_39__95_250_125_(x1);
    });
}

function $partial_2_3$Backend__Haskell___123_makeDefs_39__95_251_125_(x1, x2){
    return (function(x3){
        return Backend__Haskell___123_makeDefs_39__95_251_125_(x1, x2, x3);
    });
}

function $partial_0_1$Backend__Haskell___123_makeDefs_39__95_258_125_(){
    return (function(x1){
        return Backend__Haskell___123_makeDefs_39__95_258_125_(x1);
    });
}

function $partial_1_2$Backend__Haskell___123_makeDefs_39__95_267_125_(x1){
    return (function(x2){
        return Backend__Haskell___123_makeDefs_39__95_267_125_(x1, x2);
    });
}

function $partial_0_1$Backend__Haskell___123_makeDefs_39__95_270_125_(){
    return (function(x1){
        return Backend__Haskell___123_makeDefs_39__95_270_125_(x1);
    });
}

function $partial_0_1$Backend__Haskell___123_makeDefs_39__95_271_125_(){
    return (function(x1){
        return Backend__Haskell___123_makeDefs_39__95_271_125_(x1);
    });
}

function $partial_0_1$Backend__Haskell___123_makeDefs_39__95_272_125_(){
    return (function(x1){
        return Backend__Haskell___123_makeDefs_39__95_272_125_(x1);
    });
}

function $partial_4_6$Backend__Haskell___123_makeDefs_39__95_273_125_(x1, x2, x3, x4){
    return (function(x5){
        return (function(x6){
            return Backend__Haskell___123_makeDefs_39__95_273_125_(x1, x2, x3, x4, x5, x6);
        });
    });
}

function $partial_0_1$Backend__Haskell___123_makeDefs_39__95_278_125_(){
    return (function(x1){
        return Backend__Haskell___123_makeDefs_39__95_278_125_(x1);
    });
}

function $partial_0_1$Backend__Haskell___123_makeDefs_39__95_279_125_(){
    return (function(x1){
        return Backend__Haskell___123_makeDefs_39__95_279_125_(x1);
    });
}

function $partial_0_1$Backend__Haskell___123_makeDefs_39__95_280_125_(){
    return (function(x1){
        return Backend__Haskell___123_makeDefs_39__95_280_125_(x1);
    });
}

function $partial_3_5$Backend__Haskell___123_makeDefs_39__95_281_125_(x1, x2, x3){
    return (function(x4){
        return (function(x5){
            return Backend__Haskell___123_makeDefs_39__95_281_125_(x1, x2, x3, x4, x5);
        });
    });
}

function $partial_1_2$Backend__JSON___123_makeDefs_39__95_284_125_(x1){
    return (function(x2){
        return Backend__JSON___123_makeDefs_39__95_284_125_(x1, x2);
    });
}

function $partial_0_1$Backend__JSON___123_makeDefs_39__95_301_125_(){
    return (function(x1){
        return Backend__JSON___123_makeDefs_39__95_301_125_(x1);
    });
}

function $partial_2_4$Backend__JSON___123_makeDefs_39__95_302_125_(x1, x2){
    return (function(x3){
        return (function(x4){
            return Backend__JSON___123_makeDefs_39__95_302_125_(x1, x2, x3, x4);
        });
    });
}

function $partial_2_4$Backend__JSON___123_makeDefs_39__95_307_125_(x1, x2){
    return (function(x3){
        return (function(x4){
            return Backend__JSON___123_makeDefs_39__95_307_125_(x1, x2, x3, x4);
        });
    });
}

function $partial_2_3$Backend__ReasonML___123_makeDefs_39__95_313_125_(x1, x2){
    return (function(x3){
        return Backend__ReasonML___123_makeDefs_39__95_313_125_(x1, x2, x3);
    });
}

function $partial_1_2$Backend__ReasonML___123_makeDefs_39__95_329_125_(x1){
    return (function(x2){
        return Backend__ReasonML___123_makeDefs_39__95_329_125_(x1, x2);
    });
}

function $partial_5_7$Backend__ReasonML___123_makeDefs_39__95_335_125_(x1, x2, x3, x4, x5){
    return (function(x6){
        return (function(x7){
            return Backend__ReasonML___123_makeDefs_39__95_335_125_(x1, x2, x3, x4, x5, x6, x7);
        });
    });
}

function $partial_3_5$Backend__ReasonML___123_makeDefs_39__95_343_125_(x1, x2, x3){
    return (function(x4){
        return (function(x5){
            return Backend__ReasonML___123_makeDefs_39__95_343_125_(x1, x2, x3, x4, x5);
        });
    });
}

function $partial_0_2$Typedefs___123_makeName_95_348_125_(){
    return (function(x1){
        return (function(x2){
            return Typedefs___123_makeName_95_348_125_(x1, x2);
        });
    });
}

function $partial_0_2$Backend__JSON___123_makeSubSchema_95_358_125_(){
    return (function(x1){
        return (function(x2){
            return Backend__JSON___123_makeSubSchema_95_358_125_(x1, x2);
        });
    });
}

function $partial_0_1$Backend__Haskell___123_makeType_95_360_125_(){
    return (function(x1){
        return Backend__Haskell___123_makeType_95_360_125_(x1);
    });
}

function $partial_0_2$Backend__Haskell___123_makeType_95_361_125_(){
    return (function(x1){
        return (function(x2){
            return Backend__Haskell___123_makeType_95_361_125_(x1, x2);
        });
    });
}

function $partial_0_1$Backend__ReasonML___123_makeType_95_363_125_(){
    return (function(x1){
        return Backend__ReasonML___123_makeType_95_363_125_(x1);
    });
}

function $partial_0_1$Backend__ReasonML___123_makeType_95_364_125_(){
    return (function(x1){
        return Backend__ReasonML___123_makeType_95_364_125_(x1);
    });
}

function $partial_0_2$Backend__ReasonML___123_makeType_95_365_125_(){
    return (function(x1){
        return (function(x2){
            return Backend__ReasonML___123_makeType_95_365_125_(x1, x2);
        });
    });
}

function $partial_1_2$TParsec__Combinators___123_mand_95_367_125_(x1){
    return (function(x2){
        return TParsec__Combinators___123_mand_95_367_125_(x1, x2);
    });
}

function $partial_5_6$TParsec__Combinators___123_mand_95_368_125_(x1, x2, x3, x4, x5){
    return (function(x6){
        return TParsec__Combinators___123_mand_95_368_125_(x1, x2, x3, x4, x5, x6);
    });
}

function $partial_1_2$TParsec__Combinators___123_map_95_369_125_(x1){
    return (function(x2){
        return TParsec__Combinators___123_map_95_369_125_(x1, x2);
    });
}

function $partial_0_2$Backend__Utils___123_nameMu_95_370_125_(){
    return (function(x1){
        return (function(x2){
            return Backend__Utils___123_nameMu_95_370_125_(x1, x2);
        });
    });
}

function $partial_1_2$Backend__JSON___123_nary_95_372_125_(x1){
    return (function(x2){
        return Backend__JSON___123_nary_95_372_125_(x1, x2);
    });
}

function $partial_7_11$Parse___123_neComments_95_374_125_(x1, x2, x3, x4, x5, x6, x7){
    return (function(x8){
        return (function(x9){
            return (function(x10){
                return (function(x11){
                    return Parse___123_neComments_95_374_125_(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11);
                });
            });
        });
    });
}

function $partial_7_11$Parse___123_neComments_95_375_125_(x1, x2, x3, x4, x5, x6, x7){
    return (function(x8){
        return (function(x9){
            return (function(x10){
                return (function(x11){
                    return Parse___123_neComments_95_375_125_(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11);
                });
            });
        });
    });
}

function $partial_0_1$TParsec__Combinators___123_nelist_95_376_125_(){
    return (function(x1){
        return TParsec__Combinators___123_nelist_95_376_125_(x1);
    });
}

function $partial_1_3$TParsec__Combinators___123_nelist_95_377_125_(x1){
    return (function(x2){
        return (function(x3){
            return TParsec__Combinators___123_nelist_95_377_125_(x1, x2, x3);
        });
    });
}

function $partial_2_5$TParsec__Combinators___123_nelist_95_378_125_(x1, x2){
    return (function(x3){
        return (function(x4){
            return (function(x5){
                return TParsec__Combinators___123_nelist_95_378_125_(x1, x2, x3, x4, x5);
            });
        });
    });
}

function $partial_2_5$TParsec__Combinators___123_nelist_95_379_125_(x1, x2){
    return (function(x3){
        return (function(x4){
            return (function(x5){
                return TParsec__Combinators___123_nelist_95_379_125_(x1, x2, x3, x4, x5);
            });
        });
    });
}

function $partial_0_1$TParsec__Combinators___123_optand_95_380_125_(){
    return (function(x1){
        return TParsec__Combinators___123_optand_95_380_125_(x1);
    });
}

function $partial_0_1$TParsec__Combinators___123_optand_95_382_125_(){
    return (function(x1){
        return TParsec__Combinators___123_optand_95_382_125_(x1);
    });
}

function $partial_7_11$TParsec__Combinators__Chars___123_parens_95_383_125_(x1, x2, x3, x4, x5, x6, x7){
    return (function(x8){
        return (function(x9){
            return (function(x10){
                return (function(x11){
                    return TParsec__Combinators__Chars___123_parens_95_383_125_(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11);
                });
            });
        });
    });
}

function $partial_0_4$TParsec__Running___123_parseMaybe_95_384_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return (function(x4){
                    return TParsec__Running___123_parseMaybe_95_384_125_(x1, x2, x3, x4);
                });
            });
        });
    });
}

function $partial_0_2$TParsec__Running___123_parseMaybe_95_385_125_(){
    return (function(x1){
        return (function(x2){
            return TParsec__Running___123_parseMaybe_95_385_125_(x1, x2);
        });
    });
}

function $partial_0_4$TParsec__Running___123_parseMaybe_95_386_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return (function(x4){
                    return TParsec__Running___123_parseMaybe_95_386_125_(x1, x2, x3, x4);
                });
            });
        });
    });
}

function $partial_0_1$TParsec__Running___123_parseMaybe_95_388_125_(){
    return (function(x1){
        return TParsec__Running___123_parseMaybe_95_388_125_(x1);
    });
}

function $partial_0_2$Parse___123_parseTNamed_95_389_125_(){
    return (function(x1){
        return (function(x2){
            return Parse___123_parseTNamed_95_389_125_(x1, x2);
        });
    });
}

function $partial_0_2$Parse___123_parseTNamed_95_390_125_(){
    return (function(x1){
        return (function(x2){
            return Parse___123_parseTNamed_95_390_125_(x1, x2);
        });
    });
}

function $partial_0_1$Parse___123_parseTNamed_95_391_125_(){
    return (function(x1){
        return Parse___123_parseTNamed_95_391_125_(x1);
    });
}

function $partial_0_1$Parse___123_parseTNamed_95_392_125_(){
    return (function(x1){
        return Parse___123_parseTNamed_95_392_125_(x1);
    });
}

function $partial_0_1$Backend__JSON___123_productSubSchema_95_395_125_(){
    return (function(x1){
        return Backend__JSON___123_productSubSchema_95_395_125_(x1);
    });
}

function $partial_0_1$TParsec__Combinators___123_rand_95_399_125_(){
    return (function(x1){
        return TParsec__Combinators___123_rand_95_399_125_(x1);
    });
}

function $partial_0_1$TParsec__Combinators___123_randbindm_95_401_125_(){
    return (function(x1){
        return TParsec__Combinators___123_randbindm_95_401_125_(x1);
    });
}

function $partial_0_1$Data__Vect___123_range_95_402_125_(){
    return (function(x1){
        return Data__Vect___123_range_95_402_125_(x1);
    });
}

function $partial_0_2$Backend__Haskell___123_renderApp_95_403_125_(){
    return (function(x1){
        return (function(x2){
            return Backend__Haskell___123_renderApp_95_403_125_(x1, x2);
        });
    });
}

function $partial_0_1$Backend__Haskell___123_renderDef_95_410_125_(){
    return (function(x1){
        return Backend__Haskell___123_renderDef_95_410_125_(x1);
    });
}

function $partial_0_1$Backend__Haskell___123_renderDef_95_414_125_(){
    return (function(x1){
        return Backend__Haskell___123_renderDef_95_414_125_(x1);
    });
}

function $partial_0_1$Typedefs___123_shiftVars_95_427_125_(){
    return (function(x1){
        return Typedefs___123_shiftVars_95_427_125_(x1);
    });
}

function $partial_0_2$Language__JSON__Data___123_showString_95_428_125_(){
    return (function(x1){
        return (function(x2){
            return Language__JSON__Data___123_showString_95_428_125_(x1, x2);
        });
    });
}

function $partial_7_8$TParsec__Combinators__Chars___123_string_95_430_125_(x1, x2, x3, x4, x5, x6, x7){
    return (function(x8){
        return TParsec__Combinators__Chars___123_string_95_430_125_(x1, x2, x3, x4, x5, x6, x7, x8);
    });
}

function $partial_0_3$Parse___123_tdef_95_431_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return Parse___123_tdef_95_431_125_(x1, x2, x3);
            });
        });
    });
}

function $partial_0_4$Parse___123_tdef_95_434_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return (function(x4){
                    return Parse___123_tdef_95_434_125_(x1, x2, x3, x4);
                });
            });
        });
    });
}

function $partial_0_4$Parse___123_tdef_95_447_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return (function(x4){
                    return Parse___123_tdef_95_447_125_(x1, x2, x3, x4);
                });
            });
        });
    });
}

function $partial_0_2$Parse___123_tdef_95_448_125_(){
    return (function(x1){
        return (function(x2){
            return Parse___123_tdef_95_448_125_(x1, x2);
        });
    });
}

function $partial_0_4$Parse___123_tdef_95_462_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return (function(x4){
                    return Parse___123_tdef_95_462_125_(x1, x2, x3, x4);
                });
            });
        });
    });
}

function $partial_0_1$Parse___123_tdef_95_477_125_(){
    return (function(x1){
        return Parse___123_tdef_95_477_125_(x1);
    });
}

function $partial_0_3$Parse___123_tdef_95_491_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return Parse___123_tdef_95_491_125_(x1, x2, x3);
            });
        });
    });
}

function $partial_0_4$Parse___123_tdef_95_536_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return (function(x4){
                    return Parse___123_tdef_95_536_125_(x1, x2, x3, x4);
                });
            });
        });
    });
}

function $partial_0_2$Parse___123_tdef_95_538_125_(){
    return (function(x1){
        return (function(x2){
            return Parse___123_tdef_95_538_125_(x1, x2);
        });
    });
}

function $partial_0_2$Parse___123_tdef_95_539_125_(){
    return (function(x1){
        return (function(x2){
            return Parse___123_tdef_95_539_125_(x1, x2);
        });
    });
}

function $partial_0_2$Parse___123_tdef_95_540_125_(){
    return (function(x1){
        return (function(x2){
            return Parse___123_tdef_95_540_125_(x1, x2);
        });
    });
}

function $partial_0_1$Parse___123_tdef_95_706_125_(){
    return (function(x1){
        return Parse___123_tdef_95_706_125_(x1);
    });
}

function $partial_1_2$Parse___123_tdef_95_982_125_(x1){
    return (function(x2){
        return Parse___123_tdef_95_982_125_(x1, x2);
    });
}

function $partial_0_1$Parse___123_tdef_95_983_125_(){
    return (function(x1){
        return Parse___123_tdef_95_983_125_(x1);
    });
}

function $partial_1_2$Parse___123_tdef_95_1244_125_(x1){
    return (function(x2){
        return Parse___123_tdef_95_1244_125_(x1, x2);
    });
}

function $partial_0_1$Parse___123_tdef_95_1245_125_(){
    return (function(x1){
        return Parse___123_tdef_95_1245_125_(x1);
    });
}

function $partial_1_4$Parse___123_tdef_95_1631_125_(x1){
    return (function(x2){
        return (function(x3){
            return (function(x4){
                return Parse___123_tdef_95_1631_125_(x1, x2, x3, x4);
            });
        });
    });
}

function $partial_2_6$Parse___123_tdef_95_1632_125_(x1, x2){
    return (function(x3){
        return (function(x4){
            return (function(x5){
                return (function(x6){
                    return Parse___123_tdef_95_1632_125_(x1, x2, x3, x4, x5, x6);
                });
            });
        });
    });
}

function $partial_0_1$Parse___123_tdef_95_1636_125_(){
    return (function(x1){
        return Parse___123_tdef_95_1636_125_(x1);
    });
}

function $partial_0_1$Parse___123_tdef_95_1750_125_(){
    return (function(x1){
        return Parse___123_tdef_95_1750_125_(x1);
    });
}

function $partial_0_3$Parse___123_tdef_95_1861_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return Parse___123_tdef_95_1861_125_(x1, x2, x3);
            });
        });
    });
}

function $partial_0_3$Parse___123_tdef_95_1862_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return Parse___123_tdef_95_1862_125_(x1, x2, x3);
            });
        });
    });
}

function $partial_0_1$Parse___123_tdef_95_1866_125_(){
    return (function(x1){
        return Parse___123_tdef_95_1866_125_(x1);
    });
}

function $partial_1_5$Parse___123_tdef_95_2462_125_(x1){
    return (function(x2){
        return (function(x3){
            return (function(x4){
                return (function(x5){
                    return Parse___123_tdef_95_2462_125_(x1, x2, x3, x4, x5);
                });
            });
        });
    });
}

function $partial_1_5$Parse___123_tdef_95_2463_125_(x1){
    return (function(x2){
        return (function(x3){
            return (function(x4){
                return (function(x5){
                    return Parse___123_tdef_95_2463_125_(x1, x2, x3, x4, x5);
                });
            });
        });
    });
}

function $partial_0_1$Parse___123_tdef_95_2467_125_(){
    return (function(x1){
        return Parse___123_tdef_95_2467_125_(x1);
    });
}

function $partial_0_1$Parse___123_tdef_95_2468_125_(){
    return (function(x1){
        return Parse___123_tdef_95_2468_125_(x1);
    });
}

function $partial_1_2$Parse___123_tdef_95_2469_125_(x1){
    return (function(x2){
        return Parse___123_tdef_95_2469_125_(x1, x2);
    });
}

function $partial_0_1$Parse___123_tdef_95_2470_125_(){
    return (function(x1){
        return Parse___123_tdef_95_2470_125_(x1);
    });
}

function $partial_3_8$Parse___123_tdef_95_3437_125_(x1, x2, x3){
    return (function(x4){
        return (function(x5){
            return (function(x6){
                return (function(x7){
                    return (function(x8){
                        return Parse___123_tdef_95_3437_125_(x1, x2, x3, x4, x5, x6, x7, x8);
                    });
                });
            });
        });
    });
}

function $partial_3_7$Parse___123_tdef_95_3438_125_(x1, x2, x3){
    return (function(x4){
        return (function(x5){
            return (function(x6){
                return (function(x7){
                    return Parse___123_tdef_95_3438_125_(x1, x2, x3, x4, x5, x6, x7);
                });
            });
        });
    });
}

function $partial_1_3$Parse___123_tdef_95_3439_125_(x1){
    return (function(x2){
        return (function(x3){
            return Parse___123_tdef_95_3439_125_(x1, x2, x3);
        });
    });
}

function $partial_2_6$Parse___123_tdef_95_3440_125_(x1, x2){
    return (function(x3){
        return (function(x4){
            return (function(x5){
                return (function(x6){
                    return Parse___123_tdef_95_3440_125_(x1, x2, x3, x4, x5, x6);
                });
            });
        });
    });
}

function $partial_0_2$Parse___123_tdef_95_3441_125_(){
    return (function(x1){
        return (function(x2){
            return Parse___123_tdef_95_3441_125_(x1, x2);
        });
    });
}

function $partial_1_6$Parse___123_tnamed_95_4348_125_(x1){
    return (function(x2){
        return (function(x3){
            return (function(x4){
                return (function(x5){
                    return (function(x6){
                        return Parse___123_tnamed_95_4348_125_(x1, x2, x3, x4, x5, x6);
                    });
                });
            });
        });
    });
}

function $partial_1_5$Parse___123_tnamed_95_4349_125_(x1){
    return (function(x2){
        return (function(x3){
            return (function(x4){
                return (function(x5){
                    return Parse___123_tnamed_95_4349_125_(x1, x2, x3, x4, x5);
                });
            });
        });
    });
}

function $partial_1_5$Parse___123_tnamed_95_4350_125_(x1){
    return (function(x2){
        return (function(x3){
            return (function(x4){
                return (function(x5){
                    return Parse___123_tnamed_95_4350_125_(x1, x2, x3, x4, x5);
                });
            });
        });
    });
}

function $partial_3_5$Parse___123_tnamed_95_4385_125_(x1, x2, x3){
    return (function(x4){
        return (function(x5){
            return Parse___123_tnamed_95_4385_125_(x1, x2, x3, x4, x5);
        });
    });
}

function $partial_0_1$Parse___123_tnamed_95_4399_125_(){
    return (function(x1){
        return Parse___123_tnamed_95_4399_125_(x1);
    });
}

function $partial_0_1$Parse___123_tnamedRec_95_4403_125_(){
    return (function(x1){
        return Parse___123_tnamedRec_95_4403_125_(x1);
    });
}

function $partial_0_2$Parse___123_tnamedRec_95_4510_125_(){
    return (function(x1){
        return (function(x2){
            return Parse___123_tnamedRec_95_4510_125_(x1, x2);
        });
    });
}

function $partial_0_1$Text__PrettyPrint__WL__Core___123_toString_95_4511_125_(){
    return (function(x1){
        return Text__PrettyPrint__WL__Core___123_toString_95_4511_125_(x1);
    });
}

function $partial_7_11$TParsec__Combinators__Chars___123_withSpaces_95_4512_125_(x1, x2, x3, x4, x5, x6, x7){
    return (function(x8){
        return (function(x9){
            return (function(x10){
                return (function(x11){
                    return TParsec__Combinators__Chars___123_withSpaces_95_4512_125_(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11);
                });
            });
        });
    });
}

function $partial_3_4$Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Alternative_36_TParsecT_32_e_32_a_32_m_58__33__60__124__62__58_0_95_lam_95_5272_125_(x1, x2, x3){
    return (function(x4){
        return Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Alternative_36_TParsecT_32_e_32_a_32_m_58__33__60__124__62__58_0_95_lam_95_5272_125_(x1, x2, x3, x4);
    });
}

function $partial_2_3$Prelude__Applicative___123_TParsec__Result___64_Prelude__Applicative__Applicative_36_ResultT_32_e_32_m_58__33__60__42__62__58_0_95_lam_95_5273_125_(x1, x2){
    return (function(x3){
        return Prelude__Applicative___123_TParsec__Result___64_Prelude__Applicative__Applicative_36_ResultT_32_e_32_m_58__33__60__42__62__58_0_95_lam_95_5273_125_(x1, x2, x3);
    });
}

function $partial_2_3$Prelude__Applicative___123_TParsec__Result___64_Prelude__Applicative__Applicative_36_ResultT_32_e_32_m_58__33__60__42__62__58_0_95_lam_95_5274_125_(x1, x2){
    return (function(x3){
        return Prelude__Applicative___123_TParsec__Result___64_Prelude__Applicative__Applicative_36_ResultT_32_e_32_m_58__33__60__42__62__58_0_95_lam_95_5274_125_(x1, x2, x3);
    });
}

function $partial_2_3$Prelude__Applicative___123_Control__Monad__State___64_Prelude__Applicative__Applicative_36_StateT_32_stateType_32_f_58__33__60__42__62__58_0_95_lam_95_5275_125_(x1, x2){
    return (function(x3){
        return Prelude__Applicative___123_Control__Monad__State___64_Prelude__Applicative__Applicative_36_StateT_32_stateType_32_f_58__33__60__42__62__58_0_95_lam_95_5275_125_(x1, x2, x3);
    });
}

function $partial_2_3$Prelude__Applicative___123_Control__Monad__State___64_Prelude__Applicative__Applicative_36_StateT_32_stateType_32_f_58__33__60__42__62__58_0_95_lam_95_5276_125_(x1, x2){
    return (function(x3){
        return Prelude__Applicative___123_Control__Monad__State___64_Prelude__Applicative__Applicative_36_StateT_32_stateType_32_f_58__33__60__42__62__58_0_95_lam_95_5276_125_(x1, x2, x3);
    });
}

function $partial_1_5$Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5277_125_(x1){
    return (function(x2){
        return (function(x3){
            return (function(x4){
                return (function(x5){
                    return Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5277_125_(x1, x2, x3, x4, x5);
                });
            });
        });
    });
}

function $partial_1_3$Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5278_125_(x1){
    return (function(x2){
        return (function(x3){
            return Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5278_125_(x1, x2, x3);
        });
    });
}

function $partial_1_5$Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5279_125_(x1){
    return (function(x2){
        return (function(x3){
            return (function(x4){
                return (function(x5){
                    return Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5279_125_(x1, x2, x3, x4, x5);
                });
            });
        });
    });
}

function $partial_1_5$Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5280_125_(x1){
    return (function(x2){
        return (function(x3){
            return (function(x4){
                return (function(x5){
                    return Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5280_125_(x1, x2, x3, x4, x5);
                });
            });
        });
    });
}

function $partial_1_2$Prelude__Functor___123_TParsec__Result___64_Prelude__Functor__Functor_36_ResultT_32_e_32_m_58__33_map_58_0_95_lam_95_5281_125_(x1){
    return (function(x2){
        return Prelude__Functor___123_TParsec__Result___64_Prelude__Functor__Functor_36_ResultT_32_e_32_m_58__33_map_58_0_95_lam_95_5281_125_(x1, x2);
    });
}

function $partial_1_2$Prelude__Functor___123_Control__Monad__State___64_Prelude__Functor__Functor_36_StateT_32_stateType_32_f_58__33_map_58_0_95_lam_95_5282_125_(x1){
    return (function(x2){
        return Prelude__Functor___123_Control__Monad__State___64_Prelude__Functor__Functor_36_StateT_32_stateType_32_f_58__33_map_58_0_95_lam_95_5282_125_(x1, x2);
    });
}

function $partial_1_5$Prelude__Functor___123_TParsec__Types___64_Prelude__Functor__Functor_36_TParsecT_32_e_32_a_32_m_58__33_map_58_0_95_lam_95_5283_125_(x1){
    return (function(x2){
        return (function(x3){
            return (function(x4){
                return (function(x5){
                    return Prelude__Functor___123_TParsec__Types___64_Prelude__Functor__Functor_36_TParsecT_32_e_32_a_32_m_58__33_map_58_0_95_lam_95_5283_125_(x1, x2, x3, x4, x5);
                });
            });
        });
    });
}

function $partial_2_3$Prelude__Monad___123_TParsec__Result___64_Prelude__Monad__Monad_36_ResultT_32_e_32_m_58__33__62__62__61__58_0_95_lam_95_5284_125_(x1, x2){
    return (function(x3){
        return Prelude__Monad___123_TParsec__Result___64_Prelude__Monad__Monad_36_ResultT_32_e_32_m_58__33__62__62__61__58_0_95_lam_95_5284_125_(x1, x2, x3);
    });
}

function $partial_1_2$Prelude__Monad___123_Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0_95_lam_95_5285_125_(x1){
    return (function(x2){
        return Prelude__Monad___123_Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0_95_lam_95_5285_125_(x1, x2);
    });
}

function $partial_0_2$TParsec__Running___123_TParsec__Running___64_TParsec__Running__MonadRun_36_ResultT_32_e_32_m_58__33_runMonad_58_0_95_lam_95_5290_125_(){
    return (function(x1){
        return (function(x2){
            return TParsec__Running___123_TParsec__Running___64_TParsec__Running__MonadRun_36_ResultT_32_e_32_m_58__33_runMonad_58_0_95_lam_95_5290_125_(x1, x2);
        });
    });
}

function $partial_0_2$TParsec__Running___123_Parse___64_TParsec__Running__MonadRun_36_StateT_32_PState_32_Identity_58__33_runMonad_58_0_95_lam_95_5293_125_(){
    return (function(x1){
        return (function(x2){
            return TParsec__Running___123_Parse___64_TParsec__Running__MonadRun_36_StateT_32_PState_32_Identity_58__33_runMonad_58_0_95_lam_95_5293_125_(x1, x2);
        });
    });
}

function $partial_0_2$TParsec__Running___123_Parse___64_TParsec__Running__MonadRun_36_StateT_32_PState_32_Identity_58__33_runMonad_58_0_95_lam_95_5294_125_(){
    return (function(x1){
        return (function(x2){
            return TParsec__Running___123_Parse___64_TParsec__Running__MonadRun_36_StateT_32_PState_32_Identity_58__33_runMonad_58_0_95_lam_95_5294_125_(x1, x2);
        });
    });
}

function $partial_0_1$TParsec__Running___123_TParsec__Running___64_TParsec__Running__MonadRun_36_TParsecT_32_e_32_a_32_m_58__33_runMonad_58_0_95_lam_95_5295_125_(){
    return (function(x1){
        return TParsec__Running___123_TParsec__Running___64_TParsec__Running__MonadRun_36_TParsecT_32_e_32_a_32_m_58__33_runMonad_58_0_95_lam_95_5295_125_(x1);
    });
}

function $partial_0_1$Control__Monad__Trans___123_TParsec__Result___64_Control__Monad__Trans__MonadTrans_36_ResultT_32_e_58__33_lift_58_0_95_lam_95_5296_125_(){
    return (function(x1){
        return Control__Monad__Trans___123_TParsec__Result___64_Control__Monad__Trans__MonadTrans_36_ResultT_32_e_58__33_lift_58_0_95_lam_95_5296_125_(x1);
    });
}

function $partial_2_3$Control__Monad__Trans___123_Control__Monad__State___64_Control__Monad__Trans__MonadTrans_36_StateT_32_stateType_58__33_lift_58_0_95_lam_95_5297_125_(x1, x2){
    return (function(x3){
        return Control__Monad__Trans___123_Control__Monad__State___64_Control__Monad__Trans__MonadTrans_36_StateT_32_stateType_58__33_lift_58_0_95_lam_95_5297_125_(x1, x2, x3);
    });
}

function $partial_1_5$Control__Monad__Trans___123_TParsec__Types___64_Control__Monad__Trans__MonadTrans_36_TParsecT_32_e_32_a_58__33_lift_58_0_95_lam_95_5298_125_(x1){
    return (function(x2){
        return (function(x3){
            return (function(x4){
                return (function(x5){
                    return Control__Monad__Trans___123_TParsec__Types___64_Control__Monad__Trans__MonadTrans_36_TParsecT_32_e_32_a_58__33_lift_58_0_95_lam_95_5298_125_(x1, x2, x3, x4, x5);
                });
            });
        });
    });
}

function $partial_1_3$Control__Monad__Trans___123_TParsec__Types___64_Control__Monad__Trans__MonadTrans_36_TParsecT_32_e_32_a_58__33_lift_58_0_95_lam_95_5299_125_(x1){
    return (function(x2){
        return (function(x3){
            return Control__Monad__Trans___123_TParsec__Types___64_Control__Monad__Trans__MonadTrans_36_TParsecT_32_e_32_a_58__33_lift_58_0_95_lam_95_5299_125_(x1, x2, x3);
        });
    });
}

function $partial_0_2$Prelude__Traversable___123_Data__Vect___64_Prelude__Traversable__Traversable_36_Vect_32_n_58__33_traverse_58_0_95_lam_95_5303_125_(){
    return (function(x1){
        return (function(x2){
            return Prelude__Traversable___123_Data__Vect___64_Prelude__Traversable__Traversable_36_Vect_32_n_58__33_traverse_58_0_95_lam_95_5303_125_(x1, x2);
        });
    });
}

function $partial_8_9$Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Alternative_36_TParsecT_32_e_32_a_32_m_58__33__60__124__62__58_0(x1, x2, x3, x4, x5, x6, x7, x8){
    return (function(x9){
        return Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Alternative_36_TParsecT_32_e_32_a_32_m_58__33__60__124__62__58_0(x1, x2, x3, x4, x5, x6, x7, x8, x9);
    });
}

function $partial_6_7$Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Alternative_36_TParsecT_32_e_32_a_32_m_58__33_empty_58_0(x1, x2, x3, x4, x5, x6){
    return (function(x7){
        return Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Alternative_36_TParsecT_32_e_32_a_32_m_58__33_empty_58_0(x1, x2, x3, x4, x5, x6, x7);
    });
}

function $partial_7_8$Prelude__Applicative__Control__Monad__State___64_Prelude__Applicative__Applicative_36_StateT_32_stateType_32_f_58__33__60__42__62__58_0(x1, x2, x3, x4, x5, x6, x7){
    return (function(x8){
        return Prelude__Applicative__Control__Monad__State___64_Prelude__Applicative__Applicative_36_StateT_32_stateType_32_f_58__33__60__42__62__58_0(x1, x2, x3, x4, x5, x6, x7, x8);
    });
}

function $partial_6_7$Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33_pure_58_0(x1, x2, x3, x4, x5, x6){
    return (function(x7){
        return Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33_pure_58_0(x1, x2, x3, x4, x5, x6, x7);
    });
}

function $partial_7_8$Prelude__Functor__Control__Monad__State___64_Prelude__Functor__Functor_36_StateT_32_stateType_32_f_58__33_map_58_0(x1, x2, x3, x4, x5, x6, x7){
    return (function(x8){
        return Prelude__Functor__Control__Monad__State___64_Prelude__Functor__Functor_36_StateT_32_stateType_32_f_58__33_map_58_0(x1, x2, x3, x4, x5, x6, x7, x8);
    });
}

function $partial_7_8$Prelude__Monad__Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0(x1, x2, x3, x4, x5, x6, x7){
    return (function(x8){
        return Prelude__Monad__Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0(x1, x2, x3, x4, x5, x6, x7, x8);
    });
}

function $partial_5_6$Control__Monad__Trans__Control__Monad__State___64_Control__Monad__Trans__MonadTrans_36_StateT_32_stateType_58__33_lift_58_0(x1, x2, x3, x4, x5){
    return (function(x6){
        return Control__Monad__Trans__Control__Monad__State___64_Control__Monad__Trans__MonadTrans_36_StateT_32_stateType_58__33_lift_58_0(x1, x2, x3, x4, x5, x6);
    });
}

function $partial_0_1$$_4513_Induction__Nat__fixBox_58_go_58_0_95_lam(){
    return (function(x1){
        return $_4513_Induction__Nat__fixBox_58_go_58_0_95_lam(x1);
    });
}

function $partial_2_4$$_4514_Induction__Nat__fixBox_58_go_58_0_95_lam(x1, x2){
    return (function(x3){
        return (function(x4){
            return $_4514_Induction__Nat__fixBox_58_go_58_0_95_lam(x1, x2, x3, x4);
        });
    });
}

function $partial_3_4$$_4515_Induction__Nat__fixBox_58_go_58_0_95_lam(x1, x2, x3){
    return (function(x4){
        return $_4515_Induction__Nat__fixBox_58_go_58_0_95_lam(x1, x2, x3, x4);
    });
}

function $partial_3_4$$_4516_Backend__Utils__flattenMus_58_flattenMu_58_0_95_lam(x1, x2, x3){
    return (function(x4){
        return $_4516_Backend__Utils__flattenMus_58_flattenMu_58_0_95_lam(x1, x2, x3, x4);
    });
}

function $partial_6_7$$_4517_Text__PrettyPrint__WL__Core__render_58_best_58_0_95_lam(x1, x2, x3, x4, x5, x6){
    return (function(x7){
        return $_4517_Text__PrettyPrint__WL__Core__render_58_best_58_0_95_lam(x1, x2, x3, x4, x5, x6, x7);
    });
}

function $partial_1_2$$_4522_Parse__tdef_58_nary_58_0_95_lam(x1){
    return (function(x2){
        return $_4522_Parse__tdef_58_nary_58_0_95_lam(x1, x2);
    });
}

function $partial_1_2$$_4523_Parse__tdef_58_nary_58_0_95_lam(x1){
    return (function(x2){
        return $_4523_Parse__tdef_58_nary_58_0_95_lam(x1, x2);
    });
}

function $partial_3_8$$_5269_Parse__tdef_58_nary_58_0_95_lam(x1, x2, x3){
    return (function(x4){
        return (function(x5){
            return (function(x6){
                return (function(x7){
                    return (function(x8){
                        return $_5269_Parse__tdef_58_nary_58_0_95_lam(x1, x2, x3, x4, x5, x6, x7, x8);
                    });
                });
            });
        });
    });
}

function $partial_1_3$$_5270_Parse__tdef_58_nary_58_0_95_lam(x1){
    return (function(x2){
        return (function(x3){
            return $_5270_Parse__tdef_58_nary_58_0_95_lam(x1, x2, x3);
        });
    });
}

function $partial_3_7$$_5271_Parse__tdef_58_nary_58_0_95_lam(x1, x2, x3){
    return (function(x4){
        return (function(x5){
            return (function(x6){
                return (function(x7){
                    return $_5271_Parse__tdef_58_nary_58_0_95_lam(x1, x2, x3, x4, x5, x6, x7);
                });
            });
        });
    });
}

function $partial_2_3$Backend__JSON__disjointSubSchema_58_makeCase_58_0(x1, x2){
    return (function(x3){
        return Backend__JSON__disjointSubSchema_58_makeCase_58_0(x1, x2, x3);
    });
}

function $partial_3_4$Backend__Utils__flattenMus_58_flattenMu_58_0(x1, x2, x3){
    return (function(x4){
        return Backend__Utils__flattenMus_58_flattenMu_58_0(x1, x2, x3, x4);
    });
}

function $partial_3_4$Backend__Haskell__renderDef_58_renderConstructor_58_1(x1, x2, x3){
    return (function(x4){
        return Backend__Haskell__renderDef_58_renderConstructor_58_1(x1, x2, x3, x4);
    });
}

function $partial_3_4$Backend__ReasonML__renderDef_58_renderConstructor_58_1(x1, x2, x3){
    return (function(x4){
        return Backend__ReasonML__renderDef_58_renderConstructor_58_1(x1, x2, x3, x4);
    });
}

const $HC_0_0$MkUnit = ({type: 0});
const $HC_0_0$Refl = ({type: 0});
function $HC_2_1$Prelude__List___58__58_($1, $2){
    this.type = 1;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_2_1$Data__Vect___58__58_($1, $2){
    this.type = 1;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_2_1$Backend__Haskell__ADT($1, $2){
    this.type = 1;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_2_0$Backend__ReasonML__Alias($1, $2){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_3_1$Data__SortedMap__Branch2($1, $2, $3){
    this.type = 1;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
}

function $HC_5_2$Data__SortedMap__Branch3($1, $2, $3, $4, $5){
    this.type = 2;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
    this.$4 = $4;
    this.$5 = $5;
}

function $HC_2_4$Text__PrettyPrint__WL__Core__Cat($1, $2){
    this.type = 4;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_1_1$Text__PrettyPrint__WL__Core__Chara($1){
    this.type = 1;
    this.$1 = $1;
}

function $HC_2_1$Text__PrettyPrint__WL__Core__PrettyDoc__Chara($1, $2){
    this.type = 1;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_1_7$Text__PrettyPrint__WL__Core__Column($1){
    this.type = 7;
    this.$1 = $1;
}

const $HC_0_0$Text__PrettyPrint__WL__Core__Empty = ({type: 0});
const $HC_0_0$Text__PrettyPrint__WL__Core__PrettyDoc__Empty = ({type: 0});
function $HC_1_0$Data__SortedMap__Empty($1){
    this.type = 0;
    this.$1 = $1;
}

function $HC_1_1$Data__Fin__FS($1){
    this.type = 1;
    this.$1 = $1;
}

const $HC_0_0$Data__Fin__FZ = ({type: 0});
function $HC_1_0$TParsec__Result__HardFail($1){
    this.type = 0;
    this.$1 = $1;
}

function $HC_3_4$Backend__Haskell__HsParam($1, $2, $3){
    this.type = 4;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
}

function $HC_1_2$Backend__Haskell__HsTuple($1){
    this.type = 2;
    this.$1 = $1;
}

const $HC_0_1$Backend__Haskell__HsUnit = ({type: 1});
function $HC_1_3$Backend__Haskell__HsVar($1){
    this.type = 3;
    this.$1 = $1;
}

const $HC_0_0$Backend__Haskell__HsVoid = ({type: 0});
const $HC_0_0$Prelude__List__IsNonEmpty = ({type: 0});
function $HC_1_4$Language__JSON__Data__JArray($1){
    this.type = 4;
    this.$1 = $1;
}

function $HC_1_1$Language__JSON__Data__JBoolean($1){
    this.type = 1;
    this.$1 = $1;
}

function $HC_1_2$Language__JSON__Data__JNumber($1){
    this.type = 2;
    this.$1 = $1;
}

function $HC_1_5$Language__JSON__Data__JObject($1){
    this.type = 5;
    this.$1 = $1;
}

function $HC_1_3$Language__JSON__Data__JString($1){
    this.type = 3;
    this.$1 = $1;
}

function $HC_1_1$Prelude__Maybe__Just($1){
    this.type = 1;
    this.$1 = $1;
}

function $HC_1_1$Prelude__Nat__LTESucc($1){
    this.type = 1;
    this.$1 = $1;
}

const $HC_0_0$Prelude__Nat__LTEZero = ({type: 0});
function $HC_2_0$Data__SortedMap__Leaf($1, $2){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_1_0$Prelude__Either__Left($1){
    this.type = 0;
    this.$1 = $1;
}

function $HC_1_3$Text__PrettyPrint__WL__Core__Line($1){
    this.type = 3;
    this.$1 = $1;
}

function $HC_2_3$Text__PrettyPrint__WL__Core__PrettyDoc__Line($1, $2){
    this.type = 3;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_2_1$Data__SortedMap__M($1, $2){
    this.type = 1;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_2_0$Builtins__MkDPair($1, $2){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_3_0$Backend__Utils__MkDecl($1, $2, $3){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
}

function $HC_2_0$Data__NEList__MkNEList($1, $2){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_2_0$Builtins__MkPair($1, $2){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
}

const $HC_0_0$TParsec__Types__MkPosition = ({type: 0});
function $HC_4_0$TParsec__Success__MkSuccess($1, $2, $3, $4){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
    this.$4 = $4;
}

function $HC_2_5$Text__PrettyPrint__WL__Core__Nest($1, $2){
    this.type = 5;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_1_8$Text__PrettyPrint__WL__Core__Nesting($1){
    this.type = 8;
    this.$1 = $1;
}

const $HC_0_0$Prelude__List__Nil = ({type: 0});
const $HC_0_0$Data__Vect__Nil = ({type: 0});
const $HC_0_1$Prelude__Basics__No = ({type: 1});
const $HC_0_0$Prelude__Maybe__Nothing = ({type: 0});
const $HC_0_0$Prelude__Show__Open = ({type: 0});
function $HC_3_3$Backend__ReasonML__RMLParam($1, $2, $3){
    this.type = 3;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
}

function $HC_2_1$Backend__ReasonML__RMLTuple($1, $2){
    this.type = 1;
    this.$1 = $1;
    this.$2 = $2;
}

const $HC_0_0$Backend__ReasonML__RMLUnit = ({type: 0});
function $HC_1_2$Backend__ReasonML__RMLVar($1){
    this.type = 2;
    this.$1 = $1;
}

function $HC_1_1$Prelude__Either__Right($1){
    this.type = 1;
    this.$1 = $1;
}

function $HC_1_1$TParsec__Result__SoftFail($1){
    this.type = 1;
    this.$1 = $1;
}

function $HC_2_1$Prelude__Strings__StrCons($1, $2){
    this.type = 1;
    this.$1 = $1;
    this.$2 = $2;
}

const $HC_0_0$Prelude__Strings__StrNil = ({type: 0});
function $HC_2_0$Backend__Haskell__Synonym($1, $2){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
}

const $HC_0_0$Typedefs__T0 = ({type: 0});
const $HC_0_1$Typedefs__T1 = ({type: 1});
function $HC_3_6$Typedefs__TApp($1, $2, $3){
    this.type = 6;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
}

function $HC_2_5$Typedefs__TMu($1, $2){
    this.type = 5;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_2_0$Typedefs__TName($1, $2){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_2_3$Typedefs__TProd($1, $2){
    this.type = 3;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_2_2$Typedefs__TSum($1, $2){
    this.type = 2;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_1_4$Typedefs__TVar($1){
    this.type = 4;
    this.$1 = $1;
}

function $HC_2_2$Text__PrettyPrint__WL__Core__Text($1, $2){
    this.type = 2;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_3_2$Text__PrettyPrint__WL__Core__PrettyDoc__Text($1, $2, $3){
    this.type = 2;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
}

function $HC_2_6$Text__PrettyPrint__WL__Core__Union($1, $2){
    this.type = 6;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_4_1$Parse__VMConsLess($1, $2, $3, $4){
    this.type = 1;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
    this.$4 = $4;
}

function $HC_4_2$Parse__VMConsMore($1, $2, $3, $4){
    this.type = 2;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
    this.$4 = $4;
}

function $HC_1_0$Parse__VMEnd($1){
    this.type = 0;
    this.$1 = $1;
}

function $HC_1_2$TParsec__Result__Value($1){
    this.type = 2;
    this.$1 = $1;
}

function $HC_3_1$Backend__ReasonML__Variant($1, $2, $3){
    this.type = 1;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
}

function $HC_1_0$Prelude__Basics__Yes($1){
    this.type = 0;
    this.$1 = $1;
}

function $HC_3_0$Prelude__Applicative__Alternative_95_ictor($1, $2, $3){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
}

function $HC_3_0$Prelude__Applicative__Applicative_95_ictor($1, $2, $3){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
}

function $HC_2_0$Prelude__Interfaces__Eq_95_ictor($1, $2){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_2_0$Prelude__Monad__Monad_95_ictor($1, $2){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_3_0$Prelude__Interfaces__Ord_95_ictor($1, $2, $3){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
}

// prim__floatToStr

function prim_95__95_floatToStr($_0_arg){
    return (''+($_0_arg));
}

// prim__strCons

function prim_95__95_strCons($_0_arg, $_1_arg){
    return (($_0_arg)+($_1_arg));
}

// prim__toStrBigInt

function prim_95__95_toStrBigInt($_0_arg){
    return (($_0_arg).toString());
}

// Prelude.List.++

function Prelude__List___43__43_($_0_arg, $_1_arg, $_2_arg){
    
    if(($_1_arg.type === 1)) {
        return new $HC_2_1$Prelude__List___58__58_($_1_arg.$1, Prelude__List___43__43_(null, $_1_arg.$2, $_2_arg));
    } else {
        return $_2_arg;
    }
}

// Data.Inspect.MkSizedList

function Data__Inspect__MkSizedList($_0_arg, $_1_arg){
    return $_1_arg;
}

// TParsec.Combinators.Chars.alpha

function TParsec__Combinators__Chars__alpha($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    return $partial_7_10$TParsec__Combinators__alt(null, null, null, $_2_arg, null, TParsec__Combinators__Chars__lowerAlpha(null, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, null), TParsec__Combinators__Chars__upperAlpha(null, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, null));
}

// TParsec.Combinators.Chars.alphas

function TParsec__Combinators__Chars__alphas($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_arg){
    let $cg$1 = null;
    const $cg$3 = $_3_arg.$1;
    $cg$1 = $cg$3.$1;
    return $partial_8_11$TParsec__Combinators__map(null, null, null, null, $cg$1, $partial_1_2$TParsec__Combinators__Chars___123_alphas_95_0_125_($_5_arg), null, TParsec__Combinators__nelist(null, null, null, $_2_arg, $_3_arg, $_8_arg)(TParsec__Combinators__Chars__alpha(null, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_6_arg, $_7_arg, null)));
}

// TParsec.Combinators.alt

function TParsec__Combinators__alt($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_m1, $_8_mlen, $_9_ts){
    
    return $_3_arg.$3(null)($_5_arg($_7_m1)($_8_mlen)($_9_ts))($_6_arg($_7_m1)($_8_mlen)($_9_ts));
}

// TParsec.Combinators.alts

function TParsec__Combinators__alts($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg){
    return Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $partial_5_10$TParsec__Combinators__alt(null, null, null, $_3_arg, null), $partial_1_4$TParsec__Combinators___123_alts_95_1_125_($_3_arg), $_5_arg);
}

// TParsec.Success.and

function TParsec__Success__and($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg){
    
    let $cg$2 = null;
    $cg$2 = $_4_arg.$1;
    return new $HC_4_0$TParsec__Success__MkSuccess(new $HC_2_0$Builtins__MkPair($cg$2, $_5_arg.$1), $_5_arg.$2, Prelude__Nat__lteTransitive(null, null, null, $_5_arg.$3, null), $_5_arg.$4);
}

// TParsec.Combinators.andbind

function TParsec__Combinators__andbind($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_m1, $_9_mlen, $_10_ts){
    
    return $_4_arg.$2(null)(null)($_6_arg($_8_m1)($_9_mlen)($_10_ts))($partial_2_3$TParsec__Combinators___123_andbind_95_2_125_($_4_arg, $_7_arg));
}

// TParsec.Combinators.andbindm

function TParsec__Combinators__andbindm($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_m1, $_9_mlen, $_10_ts){
    
    return $_4_arg.$2(null)(null)($_6_arg($_8_m1)($_9_mlen)($_10_ts))($partial_2_3$TParsec__Combinators___123_andbindm_95_4_125_($_4_arg, $_7_arg));
}

// TParsec.Combinators.andoptbind

function TParsec__Combinators__andoptbind($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_arg, $_9_m1, $_10_mlen, $_11_ts){
    
    return $_4_arg.$2(null)(null)($_7_arg($_9_m1)($_10_mlen)($_11_ts))($partial_3_4$TParsec__Combinators___123_andoptbind_95_6_125_($_5_arg, $_4_arg, $_8_arg));
}

// TParsec.Combinators.ands

function TParsec__Combinators__ands($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg){
    
    let $cg$2 = null;
    const $cg$4 = $_3_arg.$1;
    $cg$2 = $cg$4.$1;
    let $cg$5 = null;
    const $cg$7 = $_3_arg.$1;
    $cg$5 = $cg$7.$1;
    return Data__NEList__foldr1_58_go_58_0(null, $partial_1_3$TParsec__Combinators___123_ands_95_9_125_($_3_arg), null, null, $partial_8_11$TParsec__Combinators__map(null, null, null, null, $cg$2, $partial_0_1$TParsec__Combinators___123_ands_95_10_125_(), null, $_5_arg.$1), Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $partial_7_11$TParsec__Combinators__map(null, null, null, null, $cg$5, $partial_0_1$TParsec__Combinators___123_ands_95_10_125_(), null), $_5_arg.$2));
}

// TParsec.Combinators.anyOf

function TParsec__Combinators__anyOf($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    return TParsec__Combinators__alts(null, null, null, $_2_arg, null, Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $partial_5_6$TParsec__Combinators___123_anyOf_95_12_125_($_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg), $_6_arg));
}

// TParsec.Combinators.anyTok

function TParsec__Combinators__anyTok($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_m1, $_6_arg, $_7_ts){
    let $cg$1 = null;
    $cg$1 = $_2_arg.$2(null);
    return Prelude__Foldable__Prelude__Maybe___64_Prelude__Foldable__Foldable_36_Maybe_58__33_foldr_58_0(null, null, $partial_2_4$TParsec__Combinators___123_anyTok_95_14_125_($_2_arg, $_1_arg), $cg$1, TParsec__Success__getTok(null, null, $_3_arg, $_5_m1, $_7_ts));
}

// Typedefs.ap

function Typedefs__ap($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    let $tco$$_3_arg = $_3_arg;
    for(;;) {
        
        if(($_2_arg.type === 0)) {
            return $_2_arg;
        } else if(($_2_arg.type === 1)) {
            return $_2_arg;
        } else if(($_2_arg.type === 6)) {
            const $cg$3 = $_2_arg.$2;
            let $cg$2 = null;
            $cg$2 = $cg$3.$2;
            $tco$$_3_arg = Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_2_3$Typedefs___123_ap_95_15_125_($_0_arg, $_3_arg), $_2_arg.$3);
            $_0_arg = $_0_arg;
            $_1_arg = null;
            $_2_arg = $cg$2;
            $_3_arg = $tco$$_3_arg;
        } else if(($_2_arg.type === 5)) {
            return new $HC_2_5$Typedefs__TMu($_2_arg.$1, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_2_3$Typedefs___123_ap_95_16_125_($_0_arg, $_3_arg), $_2_arg.$2));
        } else if(($_2_arg.type === 3)) {
            return new $HC_2_3$Typedefs__TProd($_2_arg.$1, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_2_3$Typedefs___123_ap_95_15_125_($_0_arg, $_3_arg), $_2_arg.$2));
        } else if(($_2_arg.type === 2)) {
            return new $HC_2_2$Typedefs__TSum($_2_arg.$1, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_2_3$Typedefs___123_ap_95_15_125_($_0_arg, $_3_arg), $_2_arg.$2));
        } else {
            return Data__Vect__index(null, null, $_2_arg.$1, $_3_arg);
        }
    }
}

// Typedefs.apN

function Typedefs__apN($_0_arg, $_1_arg, $_2_arg){
    
    let $cg$2 = null;
    if((Data__Vect__foldrImpl(null, null, null, $partial_0_2$Typedefs___123_apN_95_19_125_(), "", $partial_0_1$Typedefs___123_apN_95_20_125_(), Data__Vect__intersperse(null, null, ",", Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Typedefs__makeName(), Typedefs__getUsedVars(null, $_0_arg, $_2_arg, $_1_arg.$2)))) === "")) {
        $cg$2 = "";
    } else {
        $cg$2 = ("(" + (Data__Vect__foldrImpl(null, null, null, $partial_0_2$Typedefs___123_apN_95_19_125_(), "", $partial_0_1$Typedefs___123_apN_95_20_125_(), Data__Vect__intersperse(null, null, ",", Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Typedefs__makeName(), Typedefs__getUsedVars(null, $_0_arg, $_2_arg, $_1_arg.$2)))) + ")"));
    }
    
    return new $HC_2_0$Typedefs__TName(($_1_arg.$1 + $cg$2), Typedefs__ap((new $JSRTS.jsbn.BigInteger(("0"))), null, $_1_arg.$2, $_2_arg));
}

// Prelude.Bits.b16ToHexString

function Prelude__Bits__b16ToHexString($_0_arg){
    return Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $partial_0_2$Prelude__Bits___123_b16ToHexString_95_23_125_(), "", new $HC_2_1$Prelude__List___58__58_((((($_0_arg) >>> ((8 & 0xFFFF)))) & 0xFF), new $HC_2_1$Prelude__List___58__58_((($_0_arg) & 0xFF), $HC_0_0$Prelude__List__Nil)));
}

// Prelude.Bits.b8ToHexString

function Prelude__Bits__b8ToHexString($_0_arg){
    return Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $partial_0_2$prim_95__95_strCons(), "", new $HC_2_1$Prelude__List___58__58_(Prelude__Bits__b8ToHexString_58_getDigit_58_0(null, (((($_0_arg) >>> ((4 & 0xFF)))) & ((15 & 0xFF)))), new $HC_2_1$Prelude__List___58__58_(Prelude__Bits__b8ToHexString_58_getDigit_58_0(null, (($_0_arg) & ((15 & 0xFF)))), $HC_0_0$Prelude__List__Nil)));
}

// TParsec.Combinators.Chars.char

function TParsec__Combinators__Chars__char($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_in){
    return $partial_7_8$TParsec__Combinators__exact(null, $_1_arg, $_2_arg, $_3_arg, $_6_arg, $_5_arg, $_4_arg($_7_in));
}

// Text.PrettyPrint.WL.Core.char

function Text__PrettyPrint__WL__Core__char($_0_arg){
    
    if(($_0_arg === "\n")) {
        return new $HC_1_3$Text__PrettyPrint__WL__Core__Line(false);
    } else {
        return new $HC_1_1$Text__PrettyPrint__WL__Core__Chara($_0_arg);
    }
}

// Prelude.Chars.chr

function Prelude__Chars__chr($_0_arg){
    let $cg$1 = null;
    if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Int_58__33_compare_58_0($_0_arg, 0) > 0)) {
        $cg$1 = true;
    } else {
        $cg$1 = ($_0_arg === 0);
    }
    
    let $cg$2 = null;
    if($cg$1) {
        $cg$2 = (!(!(Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Int_58__33_compare_58_0($_0_arg, 1114112) < 0)));
    } else {
        $cg$2 = false;
    }
    
    
    if($cg$2) {
        return String.fromCharCode($_0_arg);
    } else {
        return "\x00";
    }
}

// Parse.comments

function Parse__comments($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    return $partial_7_10$TParsec__Combinators__alt(null, null, null, $_2_arg, null, Parse__emptyComments(null, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg), Parse__neComments(null, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg));
}

// Data.NEList.consopt

function Data__NEList__consopt($_0_arg, $_1_arg, $_2_arg){
    const $cg$2 = Prelude__Functor__Prelude___64_Prelude__Functor__Functor_36_Maybe_58__33_map_58_0(null, null, $partial_0_1$Data__NEList___123_consopt_95_24_125_(), $_2_arg);
    let $cg$1 = null;
    if(($cg$2.type === 1)) {
        $cg$1 = $cg$2.$1;
    } else {
        $cg$1 = $HC_0_0$Prelude__List__Nil;
    }
    
    return new $HC_2_0$Data__NEList__MkNEList($_1_arg, $cg$1);
}

// TParsec.Combinators.Numbers.decimalDigit

function TParsec__Combinators__Numbers__decimalDigit($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    return TParsec__Combinators__alts(null, null, null, $_2_arg, null, Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $partial_6_7$TParsec__Combinators__Numbers___123_decimalDigit_95_26_125_($_3_arg, $_1_arg, $_2_arg, $_6_arg, $_5_arg, $_4_arg), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair((new $JSRTS.jsbn.BigInteger(("0"))), "0"), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair((new $JSRTS.jsbn.BigInteger(("1"))), "1"), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair((new $JSRTS.jsbn.BigInteger(("2"))), "2"), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair((new $JSRTS.jsbn.BigInteger(("3"))), "3"), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair((new $JSRTS.jsbn.BigInteger(("4"))), "4"), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair((new $JSRTS.jsbn.BigInteger(("5"))), "5"), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair((new $JSRTS.jsbn.BigInteger(("6"))), "6"), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair((new $JSRTS.jsbn.BigInteger(("7"))), "7"), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair((new $JSRTS.jsbn.BigInteger(("8"))), "8"), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair((new $JSRTS.jsbn.BigInteger(("9"))), "9"), $HC_0_0$Prelude__List__Nil))))))))))));
}

// TParsec.Combinators.Numbers.decimalNat

function TParsec__Combinators__Numbers__decimalNat($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    let $cg$1 = null;
    const $cg$3 = $_3_arg.$1;
    $cg$1 = $cg$3.$1;
    return $partial_8_11$TParsec__Combinators__map(null, null, null, null, $cg$1, $partial_0_1$TParsec__Combinators__Numbers___123_decimalNat_95_28_125_(), null, TParsec__Combinators__nelist(null, null, null, $_2_arg, $_3_arg, $_7_arg)(TParsec__Combinators__Numbers__decimalDigit(null, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, null)));
}

// Backend.JSON.disjointSubSchema

function Backend__JSON__disjointSubSchema($_0_arg, $_1_arg){
    return new $HC_1_5$Language__JSON__Data__JObject(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("oneOf", new $HC_1_4$Language__JSON__Data__JArray(Data__Vect__foldrImpl(null, null, null, $partial_0_2$Backend__JSON___123_disjointSubSchema_95_29_125_(), $HC_0_0$Prelude__List__Nil, $partial_0_1$Typedefs___123_apN_95_20_125_(), Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_2_3$Backend__JSON__disjointSubSchema_58_makeCase_58_0(null, null), $_1_arg)))), $HC_0_0$Prelude__List__Nil));
}

// Prelude.List.elemBy

function Prelude__List__elemBy($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    for(;;) {
        
        if(($_3_arg.type === 1)) {
            
            if($_1_arg($_2_arg)($_3_arg.$1)) {
                return true;
            } else {
                $_0_arg = null;
                $_1_arg = $_1_arg;
                $_2_arg = $_2_arg;
                $_3_arg = $_3_arg.$2;
            }
        } else {
            return false;
        }
    }
}

// Parse.emptyComments

function Parse__emptyComments($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    let $cg$1 = null;
    const $cg$3 = $_3_arg.$1;
    $cg$1 = $cg$3.$1;
    return $partial_8_11$TParsec__Combinators__map(null, null, null, null, $cg$1, $partial_0_1$Parse___123_emptyComments_95_33_125_(), null, TParsec__Combinators__Chars__string(null, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_6_arg, $_5_arg, ";\n", null, $_7_arg));
}

// Text.PrettyPrint.WL.Combinators.encloseSep

function Text__PrettyPrint__WL__Combinators__encloseSep($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    if(($_3_arg.type === 1)) {
        
        if(($_3_arg.$2.type === 0)) {
            return new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(new $HC_2_4$Text__PrettyPrint__WL__Core__Cat($_0_arg, $_3_arg.$1), $_1_arg);
        } else {
            return new $HC_1_7$Text__PrettyPrint__WL__Core__Column($partial_4_5$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_44_125_($_0_arg, $_3_arg, $_2_arg, $_1_arg));
        }
    } else if(($_3_arg.type === 0)) {
        return new $HC_2_4$Text__PrettyPrint__WL__Core__Cat($_0_arg, $_1_arg);
    } else {
        return new $HC_1_7$Text__PrettyPrint__WL__Core__Column($partial_4_5$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_55_125_($_0_arg, $_3_arg, $_2_arg, $_1_arg));
    }
}

// Control.Monad.State.evalState

function Control__Monad__State__evalState($_0_arg, $_1_arg, $_2_arg, $_8_in){
    const $cg$2 = $_2_arg($_8_in);
    return $cg$2.$1;
}

// TParsec.Combinators.exact

function TParsec__Combinators__exact($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    return $partial_9_12$TParsec__Combinators__guardM(null, null, null, null, $_2_arg, $_3_arg, $partial_2_3$TParsec__Combinators___123_exact_95_57_125_($_5_arg, $_6_arg), null, $partial_5_8$TParsec__Combinators__anyTok(null, $_1_arg, $_2_arg, $_4_arg, null));
}

// ParserUtils.except

function ParserUtils__except($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    return $partial_9_12$TParsec__Combinators__guardM(null, null, null, null, $_2_arg, $_3_arg, $partial_2_3$ParserUtils___123_except_95_59_125_($_5_arg, $_6_arg), null, $partial_5_8$TParsec__Combinators__anyTok(null, $_1_arg, $_2_arg, $_4_arg, null));
}

// Data.Vect.filter

function Data__Vect__filter($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    if(($_3_arg.type === 1)) {
        const $cg$3 = Data__Vect__filter(null, null, $_2_arg, $_3_arg.$2);
        
        if($_2_arg($_3_arg.$1)) {
            return new $HC_2_0$Builtins__MkDPair($cg$3.$1.add((new $JSRTS.jsbn.BigInteger(("1")))), new $HC_2_1$Data__Vect___58__58_($_3_arg.$1, $cg$3.$2));
        } else {
            return new $HC_2_0$Builtins__MkDPair($cg$3.$1, $cg$3.$2);
        }
    } else {
        return new $HC_2_0$Builtins__MkDPair((new $JSRTS.jsbn.BigInteger(("0"))), $HC_0_0$Data__Vect__Nil);
    }
}

// Data.Fin.finToInteger

function Data__Fin__finToInteger($_0_arg, $_1_arg){
    
    if(($_1_arg.type === 1)) {
        return (new $JSRTS.jsbn.BigInteger(("1"))).add(Data__Fin__finToInteger(null, $_1_arg.$1));
    } else {
        return (new $JSRTS.jsbn.BigInteger(("0")));
    }
}

// Data.Fin.finToNat

function Data__Fin__finToNat($_0_arg, $_1_arg){
    
    if(($_1_arg.type === 1)) {
        return Data__Fin__finToNat(null, $_1_arg.$1).add((new $JSRTS.jsbn.BigInteger(("1"))));
    } else {
        return (new $JSRTS.jsbn.BigInteger(("0")));
    }
}

// Text.PrettyPrint.WL.Core.fits

function Text__PrettyPrint__WL__Core__fits($_0_arg, $_1_arg){
    for(;;) {
        
        if(($_1_arg.type === 1)) {
            
            if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Int_58__33_compare_58_0($_0_arg, 0) < 0)) {
                return false;
            } else {
                $_0_arg = ($_0_arg - 1);
                $_1_arg = $_1_arg.$2;
            }
        } else if(($_1_arg.type === 0)) {
            return (!(Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Int_58__33_compare_58_0($_0_arg, 0) < 0));
        } else if(($_1_arg.type === 3)) {
            return (!(Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Int_58__33_compare_58_0($_0_arg, 0) < 0));
        } else {
            
            if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Int_58__33_compare_58_0($_0_arg, 0) < 0)) {
                return false;
            } else {
                $_0_arg = ($_0_arg - $_1_arg.$1);
                $_1_arg = $_1_arg.$3;
            }
        }
    }
}

// Induction.Nat.fix

function Induction__Nat__fix($_0_arg, $_1_arg, $_2_arg){
    return Induction__Nat__fixBox_58_go_58_0(null, $_1_arg, null, $_2_arg.add((new $JSRTS.jsbn.BigInteger(("1")))), $_2_arg)(Prelude__Nat__lteRefl($_2_arg.add((new $JSRTS.jsbn.BigInteger(("1"))))));
}

// Text.PrettyPrint.WL.Core.flatten

function Text__PrettyPrint__WL__Core__flatten($_0_arg){
    for(;;) {
        
        if(($_0_arg.type === 4)) {
            return new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__flatten($_0_arg.$1), Text__PrettyPrint__WL__Core__flatten($_0_arg.$2));
        } else if(($_0_arg.type === 7)) {
            return new $HC_1_7$Text__PrettyPrint__WL__Core__Column($partial_1_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_34_125_($_0_arg.$1));
        } else if(($_0_arg.type === 3)) {
            
            if($_0_arg.$1) {
                return $HC_0_0$Text__PrettyPrint__WL__Core__Empty;
            } else {
                return new $HC_2_2$Text__PrettyPrint__WL__Core__Text(1, " ");
            }
        } else if(($_0_arg.type === 5)) {
            return new $HC_2_5$Text__PrettyPrint__WL__Core__Nest($_0_arg.$1, Text__PrettyPrint__WL__Core__flatten($_0_arg.$2));
        } else if(($_0_arg.type === 8)) {
            return new $HC_1_8$Text__PrettyPrint__WL__Core__Nesting($partial_1_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_34_125_($_0_arg.$1));
        } else if(($_0_arg.type === 6)) {
            $_0_arg = $_0_arg.$1;
        } else {
            return $_0_arg;
        }
    }
}

// Backend.Utils.foldr1'

function Backend__Utils__foldr1_39_($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    const $cg$3 = $_3_arg.$2;
    if(($cg$3.type === 1)) {
        return $_2_arg($_3_arg.$1)(Backend__Utils__foldr1_39_(null, null, $_2_arg, new $HC_2_1$Data__Vect___58__58_($cg$3.$1, $cg$3.$2)));
    } else {
        return $_3_arg.$1;
    }
}

// Data.Vect.foldrImpl

function Data__Vect__foldrImpl($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg){
    let $tco$$_5_arg = $_5_arg;
    for(;;) {
        
        if(($_6_arg.type === 1)) {
            $tco$$_5_arg = $partial_3_4$Data__Vect___123_foldrImpl_95_62_125_($_5_arg, $_3_arg, $_6_arg.$1);
            $_0_arg = null;
            $_1_arg = null;
            $_2_arg = null;
            $_3_arg = $_3_arg;
            $_4_arg = $_4_arg;
            $_5_arg = $tco$$_5_arg;
            $_6_arg = $_6_arg.$2;
        } else {
            return $_5_arg($_4_arg);
        }
    }
}

// Backend.Utils.freshEnv

function Backend__Utils__freshEnv($_0_arg, $_1_arg){
    return Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_1_2$Backend__Utils___123_freshEnv_95_63_125_($_1_arg), Data__Vect__range($_0_arg));
}

// Data.Vect.fromList

function Data__Vect__fromList($_0_arg, $_1_arg){
    return Data__Vect__reverse_58_go_58_0(null, null, null, null, null, $HC_0_0$Data__Vect__Nil, Data__Vect__fromList_39_(null, null, $HC_0_0$Data__Vect__Nil, $_1_arg));
}

// Data.Vect.fromList'

function Data__Vect__fromList_39_($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    for(;;) {
        
        if(($_3_arg.type === 1)) {
            $_0_arg = null;
            $_1_arg = null;
            $_2_arg = new $HC_2_1$Data__Vect___58__58_($_3_arg.$1, $_2_arg);
            $_3_arg = $_3_arg.$2;
        } else {
            return $_2_arg;
        }
    }
}

// Main.generateCode

function Main__generateCode($_0_arg, $_1_arg){
    
    if(($_0_arg === "haskell")) {
        
        return Text__PrettyPrint__WL__Core__toString(0.4, 120, Backend__generateDefs(null, null, null, $partial_1_2$Main___123_generateCode_95_64_125_($_1_arg.$1), $partial_0_1$Backend__Haskell__renderDef(), $_1_arg.$2));
    } else if(($_0_arg === "json")) {
        
        const $cg$5 = $_1_arg.$1;
        if($cg$5.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
            const $cg$7 = $_1_arg.$2;
            let $cg$6 = null;
            $cg$6 = $cg$7.$1;
            return Text__PrettyPrint__WL__Core__toString(0.4, 120, Backend__Backend__JSON___64_Backend__CodegenInterdep_36_JSONDef_58_JSON_58__33_sourceCode_58_0(new $HC_1_5$Language__JSON__Data__JObject(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("$ref", new $HC_1_3$Language__JSON__Data__JString(("#/definitions/" + $cg$6))), $HC_0_0$Prelude__List__Nil)), Control__Monad__State__evalState(null, null, Backend__JSON__makeDefs_39_($_1_arg.$2), $HC_0_0$Prelude__List__Nil)));
        } else {
            const $_10_in = $_1_arg.$1.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
            return "<error : can\'t generate JSON schema for open typedef>";
        }
    } else if(($_0_arg === "reasonml")) {
        
        return Text__PrettyPrint__WL__Core__toString(0.4, 120, Backend__generateDefs(null, null, null, $partial_1_2$Main___123_generateCode_95_65_125_($_1_arg.$1), $partial_0_1$Backend__ReasonML__renderDef(), $_1_arg.$2));
    } else {
        return "<error : unknown backend>";
    }
}

// Backend.generateDefs

function Backend__generateDefs($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg){
    const $cg$2 = Text__PrettyPrint__WL__Combinators__punctuate(new $HC_1_3$Text__PrettyPrint__WL__Core__Line(false), Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $_4_arg, $_3_arg($_5_arg)));
    if(($cg$2.type === 1)) {
        return Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldl_58_0(null, null, $partial_0_2$Backend___123_generateDefs_95_66_125_(), $cg$2.$1, $cg$2.$2);
    } else {
        return $HC_0_0$Text__PrettyPrint__WL__Core__Empty;
    }
}

// TParsec.Success.getTok

function TParsec__Success__getTok($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    return Prelude__Functor__Prelude___64_Prelude__Functor__Functor_36_Maybe_58__33_map_58_0(null, null, $partial_1_2$TParsec__Success___123_getTok_95_67_125_($_3_arg), $_2_arg($_3_arg)($_4_arg));
}

// Typedefs.getUsedIndices

function Typedefs__getUsedIndices($_0_arg, $_1_arg){
    
    if(($_1_arg.type === 0)) {
        return $HC_0_0$Prelude__List__Nil;
    } else if(($_1_arg.type === 1)) {
        return $HC_0_0$Prelude__List__Nil;
    } else if(($_1_arg.type === 6)) {
        const $cg$3 = $_1_arg.$2;
        let $cg$2 = null;
        $cg$2 = $cg$3.$2;
        return Prelude__List__nubBy_58_nubBy_39__58_0(null, $HC_0_0$Prelude__List__Nil, $partial_1_3$Typedefs___123_getUsedIndices_95_68_125_($_0_arg), Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $partial_1_3$Typedefs___123_getUsedIndices_95_69_125_($_0_arg), $HC_0_0$Prelude__List__Nil, Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $partial_1_2$Typedefs___123_getUsedIndices_95_70_125_($_1_arg.$3), Typedefs__getUsedIndices($_1_arg.$1, $cg$2))));
    } else if(($_1_arg.type === 5)) {
        return Prelude__List__nubBy_58_nubBy_39__58_0(null, $HC_0_0$Prelude__List__Nil, $partial_1_3$Typedefs___123_getUsedIndices_95_68_125_($_0_arg), Data__Vect__foldrImpl(null, null, null, $partial_1_3$Typedefs___123_getUsedIndices_95_73_125_($_0_arg), $HC_0_0$Prelude__List__Nil, $partial_0_1$Typedefs___123_apN_95_20_125_(), $_1_arg.$2));
    } else if(($_1_arg.type === 3)) {
        return Prelude__List__nubBy_58_nubBy_39__58_0(null, $HC_0_0$Prelude__List__Nil, $partial_1_3$Typedefs___123_getUsedIndices_95_68_125_($_0_arg), Data__Vect__foldrImpl(null, null, null, $partial_1_3$Typedefs___123_getUsedIndices_95_69_125_($_0_arg), $HC_0_0$Prelude__List__Nil, $partial_0_1$Typedefs___123_apN_95_20_125_(), $_1_arg.$2));
    } else if(($_1_arg.type === 2)) {
        return Prelude__List__nubBy_58_nubBy_39__58_0(null, $HC_0_0$Prelude__List__Nil, $partial_1_3$Typedefs___123_getUsedIndices_95_68_125_($_0_arg), Data__Vect__foldrImpl(null, null, null, $partial_1_3$Typedefs___123_getUsedIndices_95_69_125_($_0_arg), $HC_0_0$Prelude__List__Nil, $partial_0_1$Typedefs___123_apN_95_20_125_(), $_1_arg.$2));
    } else {
        return new $HC_2_1$Prelude__List___58__58_($_1_arg.$1, $HC_0_0$Prelude__List__Nil);
    }
}

// Typedefs.getUsedVars

function Typedefs__getUsedVars($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    return Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_1_2$Typedefs___123_getUsedIndices_95_70_125_($_2_arg), Data__Vect__fromList(null, Typedefs__getUsedIndices($_1_arg, $_3_arg)));
}

// TParsec.Combinators.guardM

function TParsec__Combinators__guardM($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_arg, $_9_m1, $_10_mlen, $_11_ts){
    
    return $_5_arg.$2(null)(null)($_8_arg($_9_m1)($_10_mlen)($_11_ts))($partial_3_4$TParsec__Combinators___123_guardM_95_84_125_($_4_arg, $_5_arg, $_6_arg));
}

// Backend.Haskell.guardParen

function Backend__Haskell__guardParen($_0_arg){
    
    if(($_0_arg.type === 4)) {
        
        if(($_0_arg.$3.type === 0)) {
            
            if($_0_arg.$1.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
                return Backend__Haskell__renderType(new $HC_3_4$Backend__Haskell__HsParam((new $JSRTS.jsbn.BigInteger(("0"))), $_0_arg.$2, $HC_0_0$Data__Vect__Nil));
            } else {
                return new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__char("("), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Backend__Haskell__renderType($_0_arg), Text__PrettyPrint__WL__Core__char(")")));
            }
        } else {
            return new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__char("("), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Backend__Haskell__renderType($_0_arg), Text__PrettyPrint__WL__Core__char(")")));
        }
    } else {
        return Backend__Haskell__renderType($_0_arg);
    }
}

// Prelude.List.head'

function Prelude__List__head_39_($_0_arg, $_1_arg){
    
    if(($_1_arg.type === 1)) {
        return new $HC_1_1$Prelude__Maybe__Just($_1_arg.$1);
    } else {
        return $HC_0_0$Prelude__Maybe__Nothing;
    }
}

// Typedefs.idVars

function Typedefs__idVars($_0_arg){
    
    if($_0_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
        return $HC_0_0$Data__Vect__Nil;
    } else {
        const $_1_in = $_0_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
        return Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Typedefs___123_idVars_95_87_125_(), Data__Vect__range($_1_in.add((new $JSRTS.jsbn.BigInteger(("1"))))));
    }
}

// Backend.Utils.ifNotPresent

function Backend__Utils__ifNotPresent($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    return $partial_7_8$Prelude__Monad__Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), $partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_()), $partial_0_4$Backend__Utils___123_ifNotPresent_95_91_125_()), $partial_0_1$Backend__Utils___123_ifNotPresent_95_92_125_(), $partial_3_4$Backend__Utils___123_ifNotPresent_95_106_125_($_2_arg, $_3_arg, $_4_arg));
}

// Parse.ignorespaces

function Parse__ignorespaces($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_arg, $_9_arg){
    return TParsec__Combinators__Chars__withSpaces(null, null, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_arg, TParsec__Combinators__landopt(null, null, null, null, $_4_arg, $_3_arg, null, TParsec__Combinators__roptand(null, null, null, null, $_4_arg, $_3_arg, null, Parse__comments(null, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_7_arg, $_6_arg, $_8_arg), $_9_arg), $partial_7_11$Parse___123_ignorespaces_95_107_125_($_2_arg, $_3_arg, $_4_arg, $_5_arg, $_7_arg, $_6_arg, $_8_arg)));
}

// Data.Vect.index

function Data__Vect__index($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    for(;;) {
        
        if(($_2_arg.type === 1)) {
            
            $_0_arg = null;
            $_1_arg = null;
            $_2_arg = $_2_arg.$1;
            $_3_arg = $_3_arg.$2;
        } else {
            
            return $_3_arg.$1;
        }
    }
}

// Data.SortedMap.insert

function Data__SortedMap__insert($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    
    if(($_4_arg.type === 0)) {
        return new $HC_2_1$Data__SortedMap__M($_4_arg.$1, new $HC_2_0$Data__SortedMap__Leaf($_2_arg, $_3_arg));
    } else {
        const $cg$3 = Data__SortedMap__treeInsert(null, null, $_4_arg.$1, null, $_2_arg, $_3_arg, $_4_arg.$2);
        if(($cg$3.type === 0)) {
            return new $HC_2_1$Data__SortedMap__M($_4_arg.$1, $cg$3.$1);
        } else {
            return new $HC_2_1$Data__SortedMap__M($_4_arg.$1, $cg$3.$1);
        }
    }
}

// Data.Fin.integerToFin

function Data__Fin__integerToFin($_0_arg, $_1_arg){
    
    if($_1_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
        return $HC_0_0$Prelude__Maybe__Nothing;
    } else {
        let $cg$2 = null;
        if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Integer_58__33_compare_58_0($_0_arg, (new $JSRTS.jsbn.BigInteger(("0")))) > 0)) {
            $cg$2 = true;
        } else {
            $cg$2 = $_0_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))));
        }
        
        
        if($cg$2) {
            return Data__Fin__natToFin($_0_arg, $_1_arg);
        } else {
            return $HC_0_0$Prelude__Maybe__Nothing;
        }
    }
}

// Data.Vect.intersperse

function Data__Vect__intersperse($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    if(($_3_arg.type === 1)) {
        return new $HC_2_1$Data__Vect___58__58_($_3_arg.$1, Data__Vect__intersperse_58_intersperse_39__58_1(null, null, null, null, null, null, $_2_arg, $_3_arg.$2));
    } else {
        return $_3_arg;
    }
}

// Prelude.Chars.isControl

function Prelude__Chars__isControl($_0_arg){
    let $cg$1 = null;
    if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Char_58__33_compare_58_0($_0_arg, "\x00") > 0)) {
        $cg$1 = true;
    } else {
        $cg$1 = ($_0_arg === "\x00");
    }
    
    let $cg$2 = null;
    if($cg$1) {
        
        if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Char_58__33_compare_58_0($_0_arg, "\x1f") < 0)) {
            $cg$2 = true;
        } else {
            $cg$2 = ($_0_arg === "\x1f");
        }
    } else {
        $cg$2 = false;
    }
    
    
    if($cg$2) {
        return true;
    } else {
        let $cg$5 = null;
        if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Char_58__33_compare_58_0($_0_arg, "\x7f") > 0)) {
            $cg$5 = true;
        } else {
            $cg$5 = ($_0_arg === "\x7f");
        }
        
        
        if($cg$5) {
            
            if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Char_58__33_compare_58_0($_0_arg, "\x9f") < 0)) {
                return true;
            } else {
                return ($_0_arg === "\x9f");
            }
        } else {
            return false;
        }
    }
}

// Prelude.Nat.isLTE

function Prelude__Nat__isLTE($_0_arg, $_1_arg){
    
    if($_0_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
        return new $HC_1_0$Prelude__Basics__Yes($HC_0_0$Prelude__Nat__LTEZero);
    } else {
        
        if($_1_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
            return $HC_0_1$Prelude__Basics__No;
        } else {
            const $_2_in = $_1_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
            const $cg$4 = Prelude__Nat__isLTE($_0_arg.subtract((new $JSRTS.jsbn.BigInteger(("1")))), $_2_in);
            if(($cg$4.type === 1)) {
                return $HC_0_1$Prelude__Basics__No;
            } else {
                return new $HC_1_0$Prelude__Basics__Yes(new $HC_1_1$Prelude__Nat__LTESucc($cg$4.$1));
            }
        }
    }
}

// Prelude.Chars.isLower

function Prelude__Chars__isLower($_0_arg){
    let $cg$1 = null;
    if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Char_58__33_compare_58_0($_0_arg, "a") > 0)) {
        $cg$1 = true;
    } else {
        $cg$1 = ($_0_arg === "a");
    }
    
    
    if($cg$1) {
        
        if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Char_58__33_compare_58_0($_0_arg, "z") < 0)) {
            return true;
        } else {
            return ($_0_arg === "z");
        }
    } else {
        return false;
    }
}

// Prelude.Chars.isUpper

function Prelude__Chars__isUpper($_0_arg){
    let $cg$1 = null;
    if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Char_58__33_compare_58_0($_0_arg, "A") > 0)) {
        $cg$1 = true;
    } else {
        $cg$1 = ($_0_arg === "A");
    }
    
    
    if($cg$1) {
        
        if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Char_58__33_compare_58_0($_0_arg, "Z") < 0)) {
            return true;
        } else {
            return ($_0_arg === "Z");
        }
    } else {
        return false;
    }
}

// TParsec.Combinators.land

function TParsec__Combinators__land($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_arg){
    let $cg$1 = null;
    const $cg$3 = $_4_arg.$1;
    $cg$1 = $cg$3.$1;
    return $partial_8_11$TParsec__Combinators__map(null, null, null, null, $cg$1, $partial_0_1$TParsec__Combinators___123_land_95_108_125_(), null, $partial_8_11$TParsec__Combinators__andbind(null, null, null, null, $_4_arg, null, $_7_arg, $partial_1_2$TParsec__Combinators__Numbers___123_decimalDigit_95_25_125_($_8_arg)));
}

// TParsec.Combinators.landopt

function TParsec__Combinators__landopt($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_arg){
    let $cg$1 = null;
    const $cg$3 = $_4_arg.$1;
    $cg$1 = $cg$3.$1;
    return $partial_8_11$TParsec__Combinators__map(null, null, null, null, $cg$1, $partial_0_1$TParsec__Combinators___123_land_95_108_125_(), null, $partial_9_12$TParsec__Combinators__andoptbind(null, null, null, null, $_4_arg, $_5_arg, null, $_7_arg, $partial_1_2$TParsec__Combinators__Numbers___123_decimalDigit_95_25_125_($_8_arg)));
}

// Data.Fin.last

function Data__Fin__last($_0_arg){
    
    if($_0_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
        return $HC_0_0$Data__Fin__FZ;
    } else {
        const $_1_in = $_0_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
        return new $HC_1_1$Data__Fin__FS(Data__Fin__last($_1_in));
    }
}

// Prelude.List.length

function Prelude__List__length($_0_arg, $_1_arg){
    
    if(($_1_arg.type === 1)) {
        return Prelude__List__length(null, $_1_arg.$2).add((new $JSRTS.jsbn.BigInteger(("1"))));
    } else {
        return (new $JSRTS.jsbn.BigInteger(("0")));
    }
}

// TParsec.Combinators.Chars.lowerAlpha

function TParsec__Combinators__Chars__lowerAlpha($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    const $cg$2 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0(true, true);
    let $cg$1 = null;
    if(($cg$2.type === 1)) {
        $cg$1 = $HC_0_0$Prelude__List__Nil;
    } else {
        let $cg$3 = null;
        if((((("abcdefghijklmnopqrstuvwxyz".slice(1) == "")) ? 1|0 : 0|0) === 0)) {
            $cg$3 = true;
        } else {
            $cg$3 = false;
        }
        
        const $cg$5 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$3, true);
        let $cg$4 = null;
        if(($cg$5.type === 1)) {
            $cg$4 = $HC_0_0$Prelude__Strings__StrNil;
        } else {
            $cg$4 = new $HC_2_1$Prelude__Strings__StrCons("abcdefghijklmnopqrstuvwxyz".slice(1)[0], "abcdefghijklmnopqrstuvwxyz".slice(1).slice(1));
        }
        
        $cg$1 = new $HC_2_1$Prelude__List___58__58_("abcdefghijklmnopqrstuvwxyz"[0], _95_Prelude__Strings__unpack_95_with_95_36(null, $cg$4));
    }
    
    return TParsec__Combinators__anyOf(null, $_1_arg, $_2_arg, $_3_arg, $_6_arg, $_5_arg, Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $_4_arg, $cg$1), null);
}

// Prelude.Nat.lteRefl

function Prelude__Nat__lteRefl($_0_arg){
    
    if($_0_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
        return $HC_0_0$Prelude__Nat__LTEZero;
    } else {
        const $_1_in = $_0_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
        return new $HC_1_1$Prelude__Nat__LTESucc(Prelude__Nat__lteRefl($_1_in));
    }
}

// Prelude.Nat.lteSuccRight

function Prelude__Nat__lteSuccRight($_0_arg, $_1_arg, $_2_arg){
    
    if(($_2_arg.type === 1)) {
        return new $HC_1_1$Prelude__Nat__LTESucc(Prelude__Nat__lteSuccRight(null, null, $_2_arg.$1));
    } else {
        return $_2_arg;
    }
}

// Prelude.Nat.lteTransitive

function Prelude__Nat__lteTransitive($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    
    if(($_3_arg.type === 1)) {
        return new $HC_1_1$Prelude__Nat__LTESucc(Prelude__Nat__lteTransitive(null, null, null, $_3_arg.$1, null));
    } else {
        return $_3_arg;
    }
}

// Backend.Haskell.makeDefs

function Backend__Haskell__makeDefs($_0_arg, $_1_arg){
    
    if(($_1_arg.type === 0)) {
        return $partial_0_1$Backend__Utils___123_ifNotPresent_95_105_125_();
    } else if(($_1_arg.type === 1)) {
        return $partial_0_1$Backend__Utils___123_ifNotPresent_95_105_125_();
    } else if(($_1_arg.type === 6)) {
        return $partial_7_8$Prelude__Monad__Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), $partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_()), $partial_0_4$Backend__Utils___123_ifNotPresent_95_91_125_()), Backend__Haskell__makeDefs_39_($_1_arg.$1, $_1_arg.$2), $partial_2_3$Backend__Haskell___123_makeDefs_95_135_125_($_0_arg, $_1_arg.$3));
    } else if(($_1_arg.type === 5)) {
        return Backend__Haskell__makeDefs_39_($_0_arg, new $HC_2_0$Typedefs__TName(Backend__Utils__nameMu(null, null, $_1_arg.$2), new $HC_2_5$Typedefs__TMu($_1_arg.$1, $_1_arg.$2)));
    } else if(($_1_arg.type === 3)) {
        return $partial_7_8$Prelude__Functor__Control__Monad__State___64_Prelude__Functor__Functor_36_StateT_32_stateType_32_f_58__33_map_58_0(null, null, null, null, $partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_(), $partial_0_1$Backend__Haskell___123_makeDefs_95_125_125_(), Prelude__Traversable__Data__Vect___64_Prelude__Traversable__Traversable_36_Vect_32_n_58__33_traverse_58_0(null, null, null, null, new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_127_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_128_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_133_125_()), $partial_1_2$Backend__Haskell__makeDefs($_0_arg), $_1_arg.$2));
    } else if(($_1_arg.type === 2)) {
        return $partial_7_8$Prelude__Functor__Control__Monad__State___64_Prelude__Functor__Functor_36_StateT_32_stateType_32_f_58__33_map_58_0(null, null, null, null, $partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_(), $partial_0_1$Backend__Haskell___123_makeDefs_95_125_125_(), Prelude__Traversable__Data__Vect___64_Prelude__Traversable__Traversable_36_Vect_32_n_58__33_traverse_58_0(null, null, null, null, new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_127_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_128_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_133_125_()), $partial_1_2$Backend__Haskell__makeDefs($_0_arg), $_1_arg.$2));
    } else {
        return $partial_0_1$Backend__Utils___123_ifNotPresent_95_105_125_();
    }
}

// Backend.JSON.makeDefs

function Backend__JSON__makeDefs($_0_arg){
    
    if(($_0_arg.type === 0)) {
        return Backend__Utils__ifNotPresent(null, null, new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Backend__JSON___123_makeDefs_95_161_125_(), $partial_0_2$Backend__JSON___123_makeDefs_95_162_125_()), "emptyType", $partial_0_1$Backend__JSON___123_makeDefs_95_163_125_());
    } else if(($_0_arg.type === 1)) {
        return Backend__Utils__ifNotPresent(null, null, new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Backend__JSON___123_makeDefs_95_161_125_(), $partial_0_2$Backend__JSON___123_makeDefs_95_162_125_()), "singletonType", $partial_0_1$Backend__JSON___123_makeDefs_95_166_125_());
    } else if(($_0_arg.type === 6)) {
        
        if(($_0_arg.$3.type === 0)) {
            
            if($_0_arg.$1.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
                return Backend__JSON__makeDefs_39_($_0_arg.$2);
            } else {
                return Backend__JSON__makeDefs_39_(Typedefs__apN($_0_arg.$1, $_0_arg.$2, $_0_arg.$3));
            }
        } else {
            return Backend__JSON__makeDefs_39_(Typedefs__apN($_0_arg.$1, $_0_arg.$2, $_0_arg.$3));
        }
    } else if(($_0_arg.type === 5)) {
        return Backend__JSON__makeDefs_39_(new $HC_2_0$Typedefs__TName(Backend__Utils__nameMu(null, null, $_0_arg.$2), new $HC_2_5$Typedefs__TMu($_0_arg.$1, $_0_arg.$2)));
    } else if(($_0_arg.type === 3)) {
        return $partial_7_8$Prelude__Functor__Control__Monad__State___64_Prelude__Functor__Functor_36_StateT_32_stateType_32_f_58__33_map_58_0(null, null, null, null, $partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_(), $partial_0_1$Backend__Haskell___123_makeDefs_95_125_125_(), Prelude__Traversable__Data__Vect___64_Prelude__Traversable__Traversable_36_Vect_32_n_58__33_traverse_58_0(null, null, null, null, new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_127_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_128_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_133_125_()), $partial_0_1$Backend__JSON__makeDefs(), $_0_arg.$2));
    } else {
        return $partial_7_8$Prelude__Functor__Control__Monad__State___64_Prelude__Functor__Functor_36_StateT_32_stateType_32_f_58__33_map_58_0(null, null, null, null, $partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_(), $partial_0_1$Backend__Haskell___123_makeDefs_95_125_125_(), Prelude__Traversable__Data__Vect___64_Prelude__Traversable__Traversable_36_Vect_32_n_58__33_traverse_58_0(null, null, null, null, new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_127_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_128_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_133_125_()), $partial_0_1$Backend__JSON__makeDefs(), $_0_arg.$2));
    }
}

// Backend.ReasonML.makeDefs

function Backend__ReasonML__makeDefs($_0_arg, $_1_arg){
    
    if(($_1_arg.type === 0)) {
        return Backend__ReasonML__makeDefs_39_((new $JSRTS.jsbn.BigInteger(("0"))), new $HC_2_0$Typedefs__TName("void", new $HC_2_5$Typedefs__TMu((new $JSRTS.jsbn.BigInteger(("0"))), $HC_0_0$Data__Vect__Nil)));
    } else if(($_1_arg.type === 1)) {
        return $partial_0_1$Backend__Utils___123_ifNotPresent_95_105_125_();
    } else if(($_1_arg.type === 6)) {
        return $partial_7_8$Prelude__Monad__Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), $partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_()), $partial_0_4$Backend__Utils___123_ifNotPresent_95_91_125_()), Backend__ReasonML__makeDefs_39_($_1_arg.$1, $_1_arg.$2), $partial_2_3$Backend__ReasonML___123_makeDefs_95_213_125_($_0_arg, $_1_arg.$3));
    } else if(($_1_arg.type === 5)) {
        return Backend__ReasonML__makeDefs_39_($_0_arg, new $HC_2_0$Typedefs__TName(Backend__Utils__nameMu(null, null, $_1_arg.$2), new $HC_2_5$Typedefs__TMu($_1_arg.$1, $_1_arg.$2)));
    } else if(($_1_arg.type === 3)) {
        return $partial_7_8$Prelude__Functor__Control__Monad__State___64_Prelude__Functor__Functor_36_StateT_32_stateType_32_f_58__33_map_58_0(null, null, null, null, $partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_(), $partial_0_1$Backend__Haskell___123_makeDefs_95_125_125_(), Prelude__Traversable__Data__Vect___64_Prelude__Traversable__Traversable_36_Vect_32_n_58__33_traverse_58_0(null, null, null, null, new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_127_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_128_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_133_125_()), $partial_1_2$Backend__ReasonML__makeDefs($_0_arg), $_1_arg.$2));
    } else if(($_1_arg.type === 2)) {
        return $partial_7_8$Prelude__Monad__Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), $partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_()), $partial_0_4$Backend__Utils___123_ifNotPresent_95_91_125_()), $partial_7_8$Prelude__Functor__Control__Monad__State___64_Prelude__Functor__Functor_36_StateT_32_stateType_32_f_58__33_map_58_0(null, null, null, null, $partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_(), $partial_0_1$Backend__Haskell___123_makeDefs_95_125_125_(), Prelude__Traversable__Data__Vect___64_Prelude__Traversable__Traversable_36_Vect_32_n_58__33_traverse_58_0(null, null, null, null, new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_127_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_128_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_133_125_()), $partial_1_2$Backend__ReasonML__makeDefs($_0_arg), $_1_arg.$2)), $partial_0_1$Backend__ReasonML___123_makeDefs_95_244_125_());
    } else {
        return $partial_0_1$Backend__Utils___123_ifNotPresent_95_105_125_();
    }
}

// Backend.Haskell.makeDefs'

function Backend__Haskell__makeDefs_39_($_0_arg, $_1_arg){
    
    const $cg$3 = $_1_arg.$2;
    let $cg$2 = null;
    if(($cg$3.type === 5)) {
        const $cg$5 = Data__Vect__filter(null, null, $partial_0_1$Backend__Haskell___123_makeDefs_39__95_248_125_(), Typedefs__getUsedVars(null, $_0_arg, Backend__Utils__freshEnv($_0_arg, "x"), $_1_arg.$2));
        let $cg$4 = null;
        $cg$4 = $cg$5.$1;
        const $cg$7 = Data__Vect__filter(null, null, $partial_0_1$Backend__Haskell___123_makeDefs_39__95_250_125_(), Typedefs__getUsedVars(null, $_0_arg, Backend__Utils__freshEnv($_0_arg, "x"), $_1_arg.$2));
        let $cg$6 = null;
        $cg$6 = Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Backend__Haskell___123_makeDefs_39__95_249_125_(), $cg$7.$2);
        const $_35_in = new $HC_2_1$Data__Vect___58__58_(new $HC_1_1$Prelude__Either__Right(new $HC_3_0$Backend__Utils__MkDecl($cg$4, $_1_arg.$1, $cg$6)), Backend__Utils__freshEnv($_0_arg, "x"));
        const $_49_in = Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_2_3$Backend__Haskell___123_makeDefs_39__95_251_125_($_0_arg, $_35_in), $cg$3.$2);
        $cg$2 = $partial_7_8$Prelude__Monad__Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), $partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_()), $partial_0_4$Backend__Utils___123_ifNotPresent_95_91_125_()), $partial_7_8$Prelude__Functor__Control__Monad__State___64_Prelude__Functor__Functor_36_StateT_32_stateType_32_f_58__33_map_58_0(null, null, null, null, $partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_(), $partial_0_1$Backend__Haskell___123_makeDefs_39__95_258_125_(), Prelude__Traversable__Prelude___64_Prelude__Traversable__Traversable_36_List_58__33_traverse_58_0(null, null, null, new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_127_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_128_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_133_125_()), $partial_1_2$Backend__Haskell___123_makeDefs_39__95_267_125_($_0_arg), Data__Vect__foldrImpl(null, null, null, $partial_0_2$Backend__JSON___123_disjointSubSchema_95_29_125_(), $HC_0_0$Prelude__List__Nil, $partial_0_1$Typedefs___123_apN_95_20_125_(), $cg$3.$2))), $partial_4_6$Backend__Haskell___123_makeDefs_39__95_273_125_($_0_arg, $_1_arg.$2, $_1_arg.$1, $_49_in));
    } else {
        $cg$2 = $partial_7_8$Prelude__Monad__Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), $partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_()), $partial_0_4$Backend__Utils___123_ifNotPresent_95_91_125_()), Backend__Haskell__makeDefs($_0_arg, $_1_arg.$2), $partial_3_5$Backend__Haskell___123_makeDefs_39__95_281_125_($_0_arg, $_1_arg.$2, $_1_arg.$1));
    }
    
    return Backend__Utils__ifNotPresent(null, null, new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Backend__JSON___123_makeDefs_95_161_125_(), $partial_0_2$Backend__JSON___123_makeDefs_95_162_125_()), $_1_arg.$1, $cg$2);
}

// Backend.JSON.makeDefs'

function Backend__JSON__makeDefs_39_($_0_arg){
    
    const $cg$3 = $_0_arg.$2;
    let $cg$2 = null;
    if(($cg$3.type === 5)) {
        const $_9_in = Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_1_2$Backend__JSON___123_makeDefs_39__95_284_125_($_0_arg.$1), $cg$3.$2);
        $cg$2 = $partial_7_8$Prelude__Monad__Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), $partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_()), $partial_0_4$Backend__Utils___123_ifNotPresent_95_91_125_()), $partial_7_8$Prelude__Functor__Control__Monad__State___64_Prelude__Functor__Functor_36_StateT_32_stateType_32_f_58__33_map_58_0(null, null, null, null, $partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_(), $partial_0_1$Backend__Haskell___123_makeDefs_95_125_125_(), Prelude__Traversable__Data__Vect___64_Prelude__Traversable__Traversable_36_Vect_32_n_58__33_traverse_58_0(null, null, null, null, new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_127_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_128_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_133_125_()), $partial_0_1$Backend__JSON___123_makeDefs_39__95_301_125_(), $_9_in)), $partial_2_4$Backend__JSON___123_makeDefs_39__95_302_125_($_0_arg.$1, $_9_in));
    } else {
        $cg$2 = $partial_7_8$Prelude__Monad__Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), $partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_()), $partial_0_4$Backend__Utils___123_ifNotPresent_95_91_125_()), Backend__JSON__makeDefs($_0_arg.$2), $partial_2_4$Backend__JSON___123_makeDefs_39__95_307_125_($_0_arg.$1, $_0_arg.$2));
    }
    
    return Backend__Utils__ifNotPresent(null, null, new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Backend__JSON___123_makeDefs_95_161_125_(), $partial_0_2$Backend__JSON___123_makeDefs_95_162_125_()), $_0_arg.$1, $cg$2);
}

// Backend.ReasonML.makeDefs'

function Backend__ReasonML__makeDefs_39_($_0_arg, $_1_arg){
    
    const $cg$3 = $_1_arg.$2;
    let $cg$2 = null;
    if(($cg$3.type === 5)) {
        const $cg$5 = Data__Vect__filter(null, null, $partial_0_1$Backend__Haskell___123_makeDefs_39__95_248_125_(), Typedefs__getUsedVars(null, $_0_arg, Backend__Utils__freshEnv($_0_arg, "\'x"), $_1_arg.$2));
        let $cg$4 = null;
        $cg$4 = $cg$5.$1;
        const $cg$7 = Data__Vect__filter(null, null, $partial_0_1$Backend__Haskell___123_makeDefs_39__95_250_125_(), Typedefs__getUsedVars(null, $_0_arg, Backend__Utils__freshEnv($_0_arg, "\'x"), $_1_arg.$2));
        let $cg$6 = null;
        $cg$6 = Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Backend__Haskell___123_makeDefs_39__95_249_125_(), $cg$7.$2);
        const $_35_in = new $HC_2_1$Data__Vect___58__58_(new $HC_1_1$Prelude__Either__Right(new $HC_3_0$Backend__Utils__MkDecl($cg$4, $_1_arg.$1, $cg$6)), Backend__Utils__freshEnv($_0_arg, "\'x"));
        const $_49_in = Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_2_3$Backend__ReasonML___123_makeDefs_39__95_313_125_($_0_arg, $_35_in), $cg$3.$2);
        $cg$2 = $partial_7_8$Prelude__Monad__Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), $partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_()), $partial_0_4$Backend__Utils___123_ifNotPresent_95_91_125_()), $partial_7_8$Prelude__Functor__Control__Monad__State___64_Prelude__Functor__Functor_36_StateT_32_stateType_32_f_58__33_map_58_0(null, null, null, null, $partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_(), $partial_0_1$Backend__Haskell___123_makeDefs_39__95_258_125_(), Prelude__Traversable__Prelude___64_Prelude__Traversable__Traversable_36_List_58__33_traverse_58_0(null, null, null, new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_127_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_128_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_133_125_()), $partial_1_2$Backend__ReasonML___123_makeDefs_39__95_329_125_($_0_arg), Data__Vect__foldrImpl(null, null, null, $partial_0_2$Backend__JSON___123_disjointSubSchema_95_29_125_(), $HC_0_0$Prelude__List__Nil, $partial_0_1$Typedefs___123_apN_95_20_125_(), $cg$3.$2))), $partial_5_7$Backend__ReasonML___123_makeDefs_39__95_335_125_($cg$3.$1, $_0_arg, $_1_arg.$2, $_1_arg.$1, $_49_in));
    } else {
        $cg$2 = $partial_7_8$Prelude__Monad__Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), $partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_()), $partial_0_4$Backend__Utils___123_ifNotPresent_95_91_125_()), Backend__ReasonML__makeDefs($_0_arg, $_1_arg.$2), $partial_3_5$Backend__ReasonML___123_makeDefs_39__95_343_125_($_0_arg, $_1_arg.$2, $_1_arg.$1));
    }
    
    return Backend__Utils__ifNotPresent(null, null, new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Backend__JSON___123_makeDefs_95_161_125_(), $partial_0_2$Backend__JSON___123_makeDefs_95_162_125_()), $_1_arg.$1, $cg$2);
}

// Typedefs.makeName

function Typedefs__makeName($_0_arg){
    
    if(($_0_arg.type === 0)) {
        return "void";
    } else if(($_0_arg.type === 1)) {
        return "unit";
    } else if(($_0_arg.type === 6)) {
        const $cg$5 = $_0_arg.$2;
        let $cg$4 = null;
        $cg$4 = $cg$5.$1;
        let $cg$6 = null;
        if((Data__Vect__foldrImpl(null, null, null, $partial_0_2$Typedefs___123_apN_95_19_125_(), "", $partial_0_1$Typedefs___123_apN_95_20_125_(), Data__Vect__intersperse(null, null, ",", Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Typedefs__makeName(), $_0_arg.$3))) === "")) {
            $cg$6 = "";
        } else {
            $cg$6 = ("(" + (Data__Vect__foldrImpl(null, null, null, $partial_0_2$Typedefs___123_apN_95_19_125_(), "", $partial_0_1$Typedefs___123_apN_95_20_125_(), Data__Vect__intersperse(null, null, ",", Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Typedefs__makeName(), $_0_arg.$3))) + ")"));
        }
        
        return ($cg$4 + $cg$6);
    } else if(($_0_arg.type === 5)) {
        return Data__Vect__foldrImpl(null, null, null, $partial_0_2$Typedefs___123_makeName_95_348_125_(), "", $partial_0_1$Typedefs___123_apN_95_20_125_(), $_0_arg.$2);
    } else if(($_0_arg.type === 3)) {
        let $cg$3 = null;
        if((Data__Vect__foldrImpl(null, null, null, $partial_0_2$Typedefs___123_apN_95_19_125_(), "", $partial_0_1$Typedefs___123_apN_95_20_125_(), Data__Vect__intersperse(null, null, ",", Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Typedefs__makeName(), $_0_arg.$2))) === "")) {
            $cg$3 = "";
        } else {
            $cg$3 = ("(" + (Data__Vect__foldrImpl(null, null, null, $partial_0_2$Typedefs___123_apN_95_19_125_(), "", $partial_0_1$Typedefs___123_apN_95_20_125_(), Data__Vect__intersperse(null, null, ",", Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Typedefs__makeName(), $_0_arg.$2))) + ")"));
        }
        
        return ("prod" + $cg$3);
    } else {
        let $cg$2 = null;
        if((Data__Vect__foldrImpl(null, null, null, $partial_0_2$Typedefs___123_apN_95_19_125_(), "", $partial_0_1$Typedefs___123_apN_95_20_125_(), Data__Vect__intersperse(null, null, ",", Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Typedefs__makeName(), $_0_arg.$2))) === "")) {
            $cg$2 = "";
        } else {
            $cg$2 = ("(" + (Data__Vect__foldrImpl(null, null, null, $partial_0_2$Typedefs___123_apN_95_19_125_(), "", $partial_0_1$Typedefs___123_apN_95_20_125_(), Data__Vect__intersperse(null, null, ",", Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Typedefs__makeName(), $_0_arg.$2))) + ")"));
        }
        
        return ("sum" + $cg$2);
    }
}

// Backend.JSON.makeSchema

function Backend__JSON__makeSchema($_0_arg, $_1_arg){
    
    if(($_1_arg.type === 0)) {
        return new $HC_1_5$Language__JSON__Data__JObject(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("$schema", new $HC_1_3$Language__JSON__Data__JString("http://json-schema.org/draft-07/schema#")), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("type", new $HC_1_3$Language__JSON__Data__JString("object")), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("required", new $HC_1_4$Language__JSON__Data__JArray(new $HC_2_1$Prelude__List___58__58_(new $HC_1_3$Language__JSON__Data__JString("value"), $HC_0_0$Prelude__List__Nil))), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("additionalProperties", new $HC_1_1$Language__JSON__Data__JBoolean(false)), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("properties", new $HC_1_5$Language__JSON__Data__JObject(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("value", $_0_arg), $HC_0_0$Prelude__List__Nil))), $HC_0_0$Prelude__List__Nil))))));
    } else {
        return new $HC_1_5$Language__JSON__Data__JObject(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("$schema", new $HC_1_3$Language__JSON__Data__JString("http://json-schema.org/draft-07/schema#")), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("type", new $HC_1_3$Language__JSON__Data__JString("object")), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("required", new $HC_1_4$Language__JSON__Data__JArray(new $HC_2_1$Prelude__List___58__58_(new $HC_1_3$Language__JSON__Data__JString("value"), $HC_0_0$Prelude__List__Nil))), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("additionalProperties", new $HC_1_1$Language__JSON__Data__JBoolean(false)), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("definitions", new $HC_1_5$Language__JSON__Data__JObject($_1_arg)), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("properties", new $HC_1_5$Language__JSON__Data__JObject(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("value", $_0_arg), $HC_0_0$Prelude__List__Nil))), $HC_0_0$Prelude__List__Nil)))))));
    }
}

// Backend.JSON.makeSubSchema

function Backend__JSON__makeSubSchema($_0_arg){
    
    if(($_0_arg.type === 0)) {
        return new $HC_1_5$Language__JSON__Data__JObject(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("$ref", new $HC_1_3$Language__JSON__Data__JString("#/definitions/emptyType")), $HC_0_0$Prelude__List__Nil));
    } else if(($_0_arg.type === 1)) {
        return new $HC_1_5$Language__JSON__Data__JObject(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("$ref", new $HC_1_3$Language__JSON__Data__JString("#/definitions/singletonType")), $HC_0_0$Prelude__List__Nil));
    } else if(($_0_arg.type === 6)) {
        
        if(($_0_arg.$3.type === 0)) {
            
            if($_0_arg.$1.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
                const $cg$7 = $_0_arg.$2;
                let $cg$6 = null;
                $cg$6 = $cg$7.$1;
                return new $HC_1_5$Language__JSON__Data__JObject(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("$ref", new $HC_1_3$Language__JSON__Data__JString(("#/definitions/" + $cg$6))), $HC_0_0$Prelude__List__Nil));
            } else {
                const $cg$9 = Typedefs__apN($_0_arg.$1, $_0_arg.$2, $_0_arg.$3);
                let $cg$8 = null;
                $cg$8 = $cg$9.$1;
                return new $HC_1_5$Language__JSON__Data__JObject(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("$ref", new $HC_1_3$Language__JSON__Data__JString(("#/definitions/" + $cg$8))), $HC_0_0$Prelude__List__Nil));
            }
        } else {
            const $cg$4 = Typedefs__apN($_0_arg.$1, $_0_arg.$2, $_0_arg.$3);
            let $cg$3 = null;
            $cg$3 = $cg$4.$1;
            return new $HC_1_5$Language__JSON__Data__JObject(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("$ref", new $HC_1_3$Language__JSON__Data__JString(("#/definitions/" + $cg$3))), $HC_0_0$Prelude__List__Nil));
        }
    } else if(($_0_arg.type === 5)) {
        return new $HC_1_5$Language__JSON__Data__JObject(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("$ref", new $HC_1_3$Language__JSON__Data__JString(("#/definitions/" + Backend__Utils__nameMu(null, null, $_0_arg.$2)))), $HC_0_0$Prelude__List__Nil));
    } else if(($_0_arg.type === 3)) {
        return Backend__JSON__productSubSchema(null, Backend__JSON__nary((new $JSRTS.jsbn.BigInteger(("2"))).add($_0_arg.$1), "proj"), $_0_arg.$2);
    } else {
        return Backend__JSON__disjointSubSchema(null, Data__Vect__zipWith(null, null, null, null, $partial_0_2$Backend__JSON___123_makeSubSchema_95_358_125_(), Backend__JSON__nary((new $JSRTS.jsbn.BigInteger(("2"))).add($_0_arg.$1), "case"), $_0_arg.$2));
    }
}

// Backend.Haskell.makeType

function Backend__Haskell__makeType($_0_arg, $_1_arg, $_2_arg){
    
    if(($_2_arg.type === 0)) {
        return $HC_0_0$Backend__Haskell__HsVoid;
    } else if(($_2_arg.type === 1)) {
        return $HC_0_1$Backend__Haskell__HsUnit;
    } else if(($_2_arg.type === 6)) {
        const $cg$7 = $_2_arg.$2;
        let $cg$6 = null;
        $cg$6 = $cg$7.$1;
        return new $HC_3_4$Backend__Haskell__HsParam($_2_arg.$1, $cg$6, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_2_3$Backend__Haskell__makeType($_0_arg, $_1_arg), $_2_arg.$3));
    } else if(($_2_arg.type === 5)) {
        const $_10_in = new $HC_2_5$Typedefs__TMu($_2_arg.$1, $_2_arg.$2);
        return new $HC_3_4$Backend__Haskell__HsParam(Prelude__List__length(null, Typedefs__getUsedIndices($_0_arg, $_10_in)), Backend__Utils__nameMu(null, null, $_2_arg.$2), Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Backend__Haskell___123_makeType_95_360_125_(), Typedefs__getUsedVars(null, $_0_arg, $_1_arg, $_10_in)));
    } else if(($_2_arg.type === 3)) {
        return new $HC_1_2$Backend__Haskell__HsTuple(Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_2_3$Backend__Haskell__makeType($_0_arg, $_1_arg), $_2_arg.$2));
    } else if(($_2_arg.type === 2)) {
        return Backend__Utils__foldr1_39_(null, null, $partial_0_2$Backend__Haskell___123_makeType_95_361_125_(), Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_2_3$Backend__Haskell__makeType($_0_arg, $_1_arg), $_2_arg.$2));
    } else {
        const $cg$3 = Data__Vect__index(null, null, $_2_arg.$1, $_1_arg);
        if(($cg$3.type === 0)) {
            return new $HC_1_3$Backend__Haskell__HsVar($cg$3.$1);
        } else {
            const $cg$5 = $cg$3.$1;
            return new $HC_3_4$Backend__Haskell__HsParam($cg$5.$1, $cg$5.$2, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Backend__Haskell___123_hsParam_95_86_125_(), $cg$5.$3));
        }
    }
}

// Backend.ReasonML.makeType

function Backend__ReasonML__makeType($_0_arg, $_1_arg, $_2_arg){
    
    if(($_2_arg.type === 0)) {
        return new $HC_3_3$Backend__ReasonML__RMLParam((new $JSRTS.jsbn.BigInteger(("0"))), "void", $HC_0_0$Data__Vect__Nil);
    } else if(($_2_arg.type === 1)) {
        return $HC_0_0$Backend__ReasonML__RMLUnit;
    } else if(($_2_arg.type === 6)) {
        const $cg$7 = $_2_arg.$2;
        let $cg$6 = null;
        $cg$6 = $cg$7.$1;
        return new $HC_3_3$Backend__ReasonML__RMLParam($_2_arg.$1, $cg$6, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_2_3$Backend__ReasonML__makeType($_0_arg, $_1_arg), $_2_arg.$3));
    } else if(($_2_arg.type === 5)) {
        const $_10_in = new $HC_2_5$Typedefs__TMu($_2_arg.$1, $_2_arg.$2);
        return new $HC_3_3$Backend__ReasonML__RMLParam(Prelude__List__length(null, Typedefs__getUsedIndices($_0_arg, $_10_in)), Backend__Utils__nameMu(null, null, $_2_arg.$2), Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Backend__ReasonML___123_makeType_95_364_125_(), Typedefs__getUsedVars(null, $_0_arg, $_1_arg, $_10_in)));
    } else if(($_2_arg.type === 3)) {
        return new $HC_2_1$Backend__ReasonML__RMLTuple($_2_arg.$1, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_2_3$Backend__ReasonML__makeType($_0_arg, $_1_arg), $_2_arg.$2));
    } else if(($_2_arg.type === 2)) {
        return Backend__Utils__foldr1_39_(null, null, $partial_0_2$Backend__ReasonML___123_makeType_95_365_125_(), Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_2_3$Backend__ReasonML__makeType($_0_arg, $_1_arg), $_2_arg.$2));
    } else {
        const $cg$3 = Data__Vect__index(null, null, $_2_arg.$1, $_1_arg);
        if(($cg$3.type === 0)) {
            return new $HC_1_2$Backend__ReasonML__RMLVar($cg$3.$1);
        } else {
            const $cg$5 = $cg$3.$1;
            return new $HC_3_3$Backend__ReasonML__RMLParam($cg$5.$1, $cg$5.$2, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Backend__ReasonML___123_makeType_95_363_125_(), $cg$5.$3));
        }
    }
}

// TParsec.Combinators.mand

function TParsec__Combinators__mand($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_m1, $_9_mlen, $_10_ts){
    
    return $_4_arg.$2(null)(null)($_6_arg)($partial_5_6$TParsec__Combinators___123_mand_95_368_125_($_4_arg, $_7_arg, $_8_m1, $_9_mlen, $_10_ts));
}

// TParsec.Combinators.map

function TParsec__Combinators__map($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_m1, $_9_le, $_10_ts){
    return $_4_arg(null)(null)($partial_1_2$TParsec__Combinators___123_map_95_369_125_($_5_arg))($_7_arg($_8_m1)($_9_le)($_10_ts));
}

// Backend.Utils.nameMu

function Backend__Utils__nameMu($_0_arg, $_1_arg, $_2_arg){
    return Data__Vect__foldrImpl(null, null, null, $partial_0_2$Backend__Utils___123_nameMu_95_370_125_(), "", $partial_0_1$Typedefs___123_apN_95_20_125_(), $_2_arg);
}

// Backend.JSON.nary

function Backend__JSON__nary($_0_arg, $_1_arg){
    return Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_1_2$Backend__JSON___123_nary_95_372_125_($_1_arg), Data__Vect__range($_0_arg));
}

// Data.Fin.natToFin

function Data__Fin__natToFin($_0_arg, $_1_arg){
    
    if($_0_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
        
        if($_1_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
            return $HC_0_0$Prelude__Maybe__Nothing;
        } else {
            const $_2_in = $_1_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
            return new $HC_1_1$Prelude__Maybe__Just($HC_0_0$Data__Fin__FZ);
        }
    } else {
        const $_3_in = $_0_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
        
        if($_1_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
            return $HC_0_0$Prelude__Maybe__Nothing;
        } else {
            const $_4_in = $_1_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
            const $cg$5 = Data__Fin__natToFin($_3_in, $_4_in);
            if(($cg$5.type === 1)) {
                return new $HC_1_1$Prelude__Maybe__Just(new $HC_1_1$Data__Fin__FS($cg$5.$1));
            } else {
                return $HC_0_0$Prelude__Maybe__Nothing;
            }
        }
    }
}

// Parse.neComments

function Parse__neComments($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    return TParsec__Combinators__land(null, null, null, null, $_3_arg, null, null, TParsec__Combinators__rand(null, null, null, null, $_3_arg, null, null, TParsec__Combinators__Chars__char(null, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_6_arg, $_5_arg, ";")($_7_arg), $partial_7_11$Parse___123_neComments_95_374_125_($_3_arg, $_2_arg, $_7_arg, $_1_arg, $_4_arg, $_6_arg, $_5_arg)), $partial_7_11$Parse___123_neComments_95_375_125_($_1_arg, $_2_arg, $_3_arg, $_4_arg, $_6_arg, $_5_arg, $_7_arg));
}

// TParsec.Combinators.nelist

function TParsec__Combinators__nelist($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg){
    return Induction__Nat__fix(null, $partial_2_5$TParsec__Combinators___123_nelist_95_379_125_($_4_arg, $_3_arg), $_5_arg);
}

// Prelude.List.nonEmpty

function Prelude__List__nonEmpty($_0_arg, $_1_arg){
    
    if(($_1_arg.type === 1)) {
        return new $HC_1_0$Prelude__Basics__Yes($HC_0_0$Prelude__List__IsNonEmpty);
    } else {
        return $HC_0_1$Prelude__Basics__No;
    }
}

// ParserUtils.notChar

function ParserUtils__notChar($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_in){
    return $partial_7_8$ParserUtils__except(null, $_1_arg, $_2_arg, $_3_arg, $_6_arg, $_5_arg, $_4_arg($_7_in));
}

// Prelude.Nat.notLTImpliesGTE

function Prelude__Nat__notLTImpliesGTE($_0_arg, $_1_arg, $_2_arg){
    
    if($_0_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
        return $HC_0_0$Prelude__Nat__LTEZero;
    } else {
        
        if($_1_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
            return null;
        } else {
            const $_3_in = $_1_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
            return new $HC_1_1$Prelude__Nat__LTESucc(Prelude__Nat__notLTImpliesGTE($_0_arg.subtract((new $JSRTS.jsbn.BigInteger(("1")))), $_3_in, null));
        }
    }
}

// TParsec.Combinators.optand

function TParsec__Combinators__optand($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_arg){
    let $cg$1 = null;
    const $cg$3 = $_4_arg.$1;
    $cg$1 = $cg$3.$1;
    let $cg$4 = null;
    const $cg$6 = $_4_arg.$1;
    $cg$4 = $cg$6.$1;
    return $partial_7_10$TParsec__Combinators__alt(null, null, null, $_5_arg, null, $partial_8_11$TParsec__Combinators__andbind(null, null, null, null, $_4_arg, null, $partial_8_11$TParsec__Combinators__map(null, null, null, null, $cg$1, $partial_0_1$TParsec__Combinators___123_optand_95_380_125_(), null, $_7_arg), $partial_1_6$TParsec__Combinators___123_ands_95_8_125_($_8_arg)), $partial_8_11$TParsec__Combinators__map(null, null, null, null, $cg$4, $partial_0_1$TParsec__Combinators___123_optand_95_382_125_(), null, $_8_arg));
}

// TParsec.Combinators.Chars.parens

function TParsec__Combinators__Chars__parens($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_arg, $_13_in){
    return TParsec__Combinators__land(null, null, null, null, $_4_arg, null, null, TParsec__Combinators__rand(null, null, null, null, $_4_arg, null, null, TParsec__Combinators__Chars__char(null, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, "(")($_8_arg), $_13_in), $partial_7_11$TParsec__Combinators__Chars___123_parens_95_383_125_($_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_arg));
}

// TParsec.Running.parseMaybe

function TParsec__Running__parseMaybe($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    const $cg$2 = Prelude__Traversable__Prelude___64_Prelude__Traversable__Traversable_36_List_58__33_traverse_58_0(null, null, null, new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TParsec__Running___123_parseMaybe_95_384_125_(), $partial_0_2$TParsec__Running___123_parseMaybe_95_385_125_(), $partial_0_4$TParsec__Running___123_parseMaybe_95_386_125_()), $partial_0_1$TParsec__Running___123_parseMaybe_95_388_125_(), $_3_arg(null)($_7_arg(Prelude__List__length(null, $_4_arg($_6_arg)))(Prelude__List__length(null, $_4_arg($_6_arg)))(Prelude__Nat__lteRefl(Prelude__List__length(null, $_4_arg($_6_arg))))($_5_arg($_4_arg($_6_arg)))));
    if(($cg$2.type === 1)) {
        return Prelude__List__head_39_(null, $cg$2.$1);
    } else {
        return $HC_0_0$Prelude__Maybe__Nothing;
    }
}

// Parse.parseTNamed

function Parse__parseTNamed($_0_arg){
    return TParsec__Running__parseMaybe(null, null, null, $partial_0_2$Parse___123_parseTNamed_95_390_125_(), $partial_0_1$Parse___123_parseTNamed_95_391_125_(), $partial_0_1$Parse___123_parseTNamed_95_392_125_(), $_0_arg, $partial_0_1$Parse__tnamedRec());
}

// Main.parseType

function Main__parseType(){
    return $partial_0_1$Parse__parseTNamed();
}

// Prelude.Show.primNumShow

function Prelude__Show__primNumShow($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    const $_4_in = $_1_arg($_3_arg);
    let $cg$1 = null;
    $cg$1 = (new $JSRTS.jsbn.BigInteger(("0")));
    let $cg$2 = null;
    if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Integer_58__33_compare_58_0($cg$1, (new $JSRTS.jsbn.BigInteger(("5")))) > 0)) {
        $cg$2 = true;
    } else {
        let $cg$3 = null;
        $cg$3 = (new $JSRTS.jsbn.BigInteger(("0")));
        $cg$2 = $cg$3.equals((new $JSRTS.jsbn.BigInteger(("5"))));
    }
    
    let $cg$4 = null;
    if($cg$2) {
        let $cg$5 = null;
        if((((($_4_in == "")) ? 1|0 : 0|0) === 0)) {
            $cg$5 = true;
        } else {
            $cg$5 = false;
        }
        
        const $cg$7 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$5, true);
        if(($cg$7.type === 1)) {
            $cg$4 = false;
        } else {
            $cg$4 = ($_4_in[0] === "-");
        }
    } else {
        $cg$4 = false;
    }
    
    
    if($cg$4) {
        return ("(" + ($_4_in + ")"));
    } else {
        return $_4_in;
    }
}

// Backend.JSON.productSubSchema

function Backend__JSON__productSubSchema($_0_arg, $_1_arg, $_2_arg){
    return new $HC_1_5$Language__JSON__Data__JObject(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("type", new $HC_1_3$Language__JSON__Data__JString("object")), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("required", new $HC_1_4$Language__JSON__Data__JArray(Data__Vect__foldrImpl(null, null, null, $partial_0_2$Backend__JSON___123_disjointSubSchema_95_29_125_(), $HC_0_0$Prelude__List__Nil, $partial_0_1$Typedefs___123_apN_95_20_125_(), Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Backend__JSON___123_productSubSchema_95_395_125_(), $_1_arg)))), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("additionalProperties", new $HC_1_1$Language__JSON__Data__JBoolean(false)), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("properties", new $HC_1_5$Language__JSON__Data__JObject(Data__Vect__foldrImpl(null, null, null, $partial_0_2$Backend__JSON___123_disjointSubSchema_95_29_125_(), $HC_0_0$Prelude__List__Nil, $partial_0_1$Typedefs___123_apN_95_20_125_(), Data__Vect__zipWith(null, null, null, null, $partial_0_2$Backend__JSON___123_makeSubSchema_95_358_125_(), $_1_arg, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Backend__JSON__makeSubSchema(), $_2_arg))))), $HC_0_0$Prelude__List__Nil)))));
}

// Text.PrettyPrint.WL.Combinators.punctuate

function Text__PrettyPrint__WL__Combinators__punctuate($_0_arg, $_1_arg){
    
    if(($_1_arg.type === 1)) {
        
        if(($_1_arg.$2.type === 0)) {
            return new $HC_2_1$Prelude__List___58__58_($_1_arg.$1, $HC_0_0$Prelude__List__Nil);
        } else {
            return new $HC_2_1$Prelude__List___58__58_(new $HC_2_4$Text__PrettyPrint__WL__Core__Cat($_1_arg.$1, $_0_arg), Text__PrettyPrint__WL__Combinators__punctuate($_0_arg, $_1_arg.$2));
        }
    } else {
        return $_1_arg;
    }
}

// TParsec.Combinators.rand

function TParsec__Combinators__rand($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_arg){
    let $cg$1 = null;
    const $cg$3 = $_4_arg.$1;
    $cg$1 = $cg$3.$1;
    return $partial_8_11$TParsec__Combinators__map(null, null, null, null, $cg$1, $partial_0_1$TParsec__Combinators___123_rand_95_399_125_(), null, $partial_8_11$TParsec__Combinators__andbind(null, null, null, null, $_4_arg, null, $_7_arg, $partial_1_2$TParsec__Combinators__Numbers___123_decimalDigit_95_25_125_($_8_arg)));
}

// TParsec.Combinators.randbindm

function TParsec__Combinators__randbindm($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    let $cg$1 = null;
    const $cg$3 = $_4_arg.$1;
    $cg$1 = $cg$3.$1;
    return $partial_8_11$TParsec__Combinators__map(null, null, null, null, $cg$1, $partial_0_1$TParsec__Combinators___123_randbindm_95_401_125_(), null, $partial_8_11$TParsec__Combinators__andbindm(null, null, null, null, $_4_arg, null, $_6_arg, $_7_arg));
}

// Data.Vect.range

function Data__Vect__range($_0_arg){
    
    if($_0_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
        return $HC_0_0$Data__Vect__Nil;
    } else {
        const $_1_in = $_0_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
        return new $HC_2_1$Data__Vect___58__58_($HC_0_0$Data__Fin__FZ, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Data__Vect___123_range_95_402_125_(), Data__Vect__range($_1_in)));
    }
}

// Backend.Haskell.renderApp

function Backend__Haskell__renderApp($_0_arg, $_1_arg, $_2_arg){
    let $cg$1 = null;
    if((((($_1_arg == "")) ? 1|0 : 0|0) === 0)) {
        $cg$1 = true;
    } else {
        $cg$1 = false;
    }
    
    const $cg$3 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$1, true);
    let $cg$2 = null;
    if(($cg$3.type === 1)) {
        $cg$2 = "";
    } else {
        let $cg$4 = null;
        if(Prelude__Chars__isLower($_1_arg[0])) {
            $cg$4 = String.fromCharCode(((($_1_arg[0]).charCodeAt(0)|0) - 32));
        } else {
            $cg$4 = $_1_arg[0];
        }
        
        $cg$2 = (($cg$4)+($_1_arg.slice(1)));
    }
    
    return new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__text($cg$2), Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldl_58_0(null, null, $partial_0_2$Backend__Haskell___123_renderApp_95_403_125_(), $HC_0_0$Text__PrettyPrint__WL__Core__Empty, Data__Vect__foldrImpl(null, null, null, $partial_0_2$Backend__JSON___123_disjointSubSchema_95_29_125_(), $HC_0_0$Prelude__List__Nil, $partial_0_1$Typedefs___123_apN_95_20_125_(), $_2_arg)));
}

// Backend.ReasonML.renderApp

function Backend__ReasonML__renderApp($_0_arg, $_1_arg, $_2_arg){
    let $cg$1 = null;
    if(($_2_arg.type === 0)) {
        
        if($_0_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
            $cg$1 = $HC_0_0$Text__PrettyPrint__WL__Core__Empty;
        } else {
            $cg$1 = Text__PrettyPrint__WL__Combinators__encloseSep(Text__PrettyPrint__WL__Core__char("("), Text__PrettyPrint__WL__Core__char(")"), Text__PrettyPrint__WL__Core__char(","), Data__Vect__foldrImpl(null, null, null, $partial_0_2$Backend__JSON___123_disjointSubSchema_95_29_125_(), $HC_0_0$Prelude__List__Nil, $partial_0_1$Typedefs___123_apN_95_20_125_(), $_2_arg));
        }
    } else {
        $cg$1 = Text__PrettyPrint__WL__Combinators__encloseSep(Text__PrettyPrint__WL__Core__char("("), Text__PrettyPrint__WL__Core__char(")"), Text__PrettyPrint__WL__Core__char(","), Data__Vect__foldrImpl(null, null, null, $partial_0_2$Backend__JSON___123_disjointSubSchema_95_29_125_(), $HC_0_0$Prelude__List__Nil, $partial_0_1$Typedefs___123_apN_95_20_125_(), $_2_arg));
    }
    
    return new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__text($_1_arg), $cg$1);
}

// Backend.ReasonML.renderDecl

function Backend__ReasonML__renderDecl($_0_arg){
    let $cg$1 = null;
    $cg$1 = $_0_arg.$1;
    let $cg$2 = null;
    $cg$2 = $_0_arg.$2;
    let $cg$3 = null;
    if((((($cg$2 == "")) ? 1|0 : 0|0) === 0)) {
        $cg$3 = true;
    } else {
        $cg$3 = false;
    }
    
    const $cg$5 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$3, true);
    let $cg$4 = null;
    if(($cg$5.type === 1)) {
        $cg$4 = "";
    } else {
        let $cg$6 = null;
        $cg$6 = $_0_arg.$2;
        let $cg$7 = null;
        if(Prelude__Chars__isUpper($cg$6[0])) {
            let $cg$9 = null;
            $cg$9 = $_0_arg.$2;
            $cg$7 = String.fromCharCode(((($cg$9[0]).charCodeAt(0)|0) + 32));
        } else {
            let $cg$8 = null;
            $cg$8 = $_0_arg.$2;
            $cg$7 = $cg$8[0];
        }
        
        let $cg$10 = null;
        $cg$10 = $_0_arg.$2;
        $cg$4 = (($cg$7)+($cg$10.slice(1)));
    }
    
    let $cg$11 = null;
    $cg$11 = $_0_arg.$3;
    return Backend__ReasonML__renderApp($cg$1, $cg$4, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Text__PrettyPrint__WL__Core__text(), $cg$11));
}

// Backend.Haskell.renderDef

function Backend__Haskell__renderDef($_0_arg){
    
    if(($_0_arg.type === 1)) {
        const $cg$7 = $_0_arg.$1;
        let $cg$6 = null;
        $cg$6 = $cg$7.$2;
        const $cg$9 = $_0_arg.$1;
        let $cg$8 = null;
        $cg$8 = $cg$9.$3;
        const $cg$11 = Text__PrettyPrint__WL__Combinators__punctuate(Text__PrettyPrint__WL__Core__text(" |"), Data__Vect__foldrImpl(null, null, null, $partial_0_2$Backend__JSON___123_disjointSubSchema_95_29_125_(), $HC_0_0$Prelude__List__Nil, $partial_0_1$Typedefs___123_apN_95_20_125_(), Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_3_4$Backend__Haskell__renderDef_58_renderConstructor_58_1(null, null, null), $_0_arg.$2)));
        let $cg$10 = null;
        if(($cg$11.type === 1)) {
            $cg$10 = Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldl_58_0(null, null, $partial_0_2$Backend__Haskell___123_renderApp_95_403_125_(), $cg$11.$1, $cg$11.$2);
        } else {
            $cg$10 = $HC_0_0$Text__PrettyPrint__WL__Core__Empty;
        }
        
        return new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__text("data"), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__char(" "), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Backend__Haskell__renderApp(null, $cg$6, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Backend__Haskell___123_renderDef_95_410_125_(), $cg$8)), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__char(" "), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__char("="), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__char(" "), $cg$10))))));
    } else {
        const $cg$3 = $_0_arg.$1;
        let $cg$2 = null;
        $cg$2 = $cg$3.$2;
        const $cg$5 = $_0_arg.$1;
        let $cg$4 = null;
        $cg$4 = $cg$5.$3;
        return new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__text("type"), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__char(" "), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Backend__Haskell__renderApp(null, $cg$2, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Backend__Haskell___123_renderDef_95_414_125_(), $cg$4)), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__char(" "), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__char("="), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__char(" "), Backend__Haskell__renderType($_0_arg.$2)))))));
    }
}

// Backend.ReasonML.renderDef

function Backend__ReasonML__renderDef($_0_arg){
    
    if(($_0_arg.type === 0)) {
        return new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__text("type"), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__char(" "), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Backend__ReasonML__renderDecl($_0_arg.$1), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__char(" "), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__char("="), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__char(" "), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Backend__ReasonML__renderType($_0_arg.$2), Text__PrettyPrint__WL__Core__char(";"))))))));
    } else {
        let $cg$2 = null;
        if(($_0_arg.$3.type === 0)) {
            
            if($_0_arg.$1.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
                $cg$2 = $HC_0_0$Text__PrettyPrint__WL__Core__Empty;
            } else {
                const $cg$7 = Text__PrettyPrint__WL__Combinators__punctuate(Text__PrettyPrint__WL__Core__text(" |"), Data__Vect__foldrImpl(null, null, null, $partial_0_2$Backend__JSON___123_disjointSubSchema_95_29_125_(), $HC_0_0$Prelude__List__Nil, $partial_0_1$Typedefs___123_apN_95_20_125_(), Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_3_4$Backend__ReasonML__renderDef_58_renderConstructor_58_1(null, null, null), $_0_arg.$3)));
                let $cg$6 = null;
                if(($cg$7.type === 1)) {
                    $cg$6 = Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldl_58_0(null, null, $partial_0_2$Backend__Haskell___123_renderApp_95_403_125_(), $cg$7.$1, $cg$7.$2);
                } else {
                    $cg$6 = $HC_0_0$Text__PrettyPrint__WL__Core__Empty;
                }
                
                $cg$2 = new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__char(" "), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__char("="), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__char(" "), $cg$6)));
            }
        } else {
            const $cg$4 = Text__PrettyPrint__WL__Combinators__punctuate(Text__PrettyPrint__WL__Core__text(" |"), Data__Vect__foldrImpl(null, null, null, $partial_0_2$Backend__JSON___123_disjointSubSchema_95_29_125_(), $HC_0_0$Prelude__List__Nil, $partial_0_1$Typedefs___123_apN_95_20_125_(), Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_3_4$Backend__ReasonML__renderDef_58_renderConstructor_58_1(null, null, null), $_0_arg.$3)));
            let $cg$3 = null;
            if(($cg$4.type === 1)) {
                $cg$3 = Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldl_58_0(null, null, $partial_0_2$Backend__Haskell___123_renderApp_95_403_125_(), $cg$4.$1, $cg$4.$2);
            } else {
                $cg$3 = $HC_0_0$Text__PrettyPrint__WL__Core__Empty;
            }
            
            $cg$2 = new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__char(" "), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__char("="), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__char(" "), $cg$3)));
        }
        
        return new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__text("type"), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__char(" "), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Backend__ReasonML__renderDecl($_0_arg.$2), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat($cg$2, Text__PrettyPrint__WL__Core__char(";")))));
    }
}

// Backend.Haskell.renderType

function Backend__Haskell__renderType($_0_arg){
    
    if(($_0_arg.type === 4)) {
        return Backend__Haskell__renderApp(null, $_0_arg.$2, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Backend__Haskell__guardParen(), $_0_arg.$3));
    } else if(($_0_arg.type === 2)) {
        return Text__PrettyPrint__WL__Combinators__encloseSep(Text__PrettyPrint__WL__Core__char("("), Text__PrettyPrint__WL__Core__char(")"), Text__PrettyPrint__WL__Core__char(","), Data__Vect__foldrImpl(null, null, null, $partial_0_2$Backend__JSON___123_disjointSubSchema_95_29_125_(), $HC_0_0$Prelude__List__Nil, $partial_0_1$Typedefs___123_apN_95_20_125_(), Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Backend__Haskell__renderType(), $_0_arg.$1)));
    } else if(($_0_arg.type === 1)) {
        return Text__PrettyPrint__WL__Core__text("()");
    } else if(($_0_arg.type === 3)) {
        let $cg$2 = null;
        if((((($_0_arg.$1 == "")) ? 1|0 : 0|0) === 0)) {
            $cg$2 = true;
        } else {
            $cg$2 = false;
        }
        
        const $cg$4 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$2, true);
        let $cg$3 = null;
        if(($cg$4.type === 1)) {
            $cg$3 = "";
        } else {
            let $cg$5 = null;
            if(Prelude__Chars__isUpper($_0_arg.$1[0])) {
                $cg$5 = String.fromCharCode(((($_0_arg.$1[0]).charCodeAt(0)|0) + 32));
            } else {
                $cg$5 = $_0_arg.$1[0];
            }
            
            $cg$3 = (($cg$5)+($_0_arg.$1.slice(1)));
        }
        
        return Text__PrettyPrint__WL__Core__text($cg$3);
    } else {
        return Text__PrettyPrint__WL__Core__text("Void");
    }
}

// Backend.ReasonML.renderType

function Backend__ReasonML__renderType($_0_arg){
    
    if(($_0_arg.type === 3)) {
        let $cg$2 = null;
        if((((($_0_arg.$2 == "")) ? 1|0 : 0|0) === 0)) {
            $cg$2 = true;
        } else {
            $cg$2 = false;
        }
        
        const $cg$4 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$2, true);
        let $cg$3 = null;
        if(($cg$4.type === 1)) {
            $cg$3 = "";
        } else {
            let $cg$5 = null;
            if(Prelude__Chars__isUpper($_0_arg.$2[0])) {
                $cg$5 = String.fromCharCode(((($_0_arg.$2[0]).charCodeAt(0)|0) + 32));
            } else {
                $cg$5 = $_0_arg.$2[0];
            }
            
            $cg$3 = (($cg$5)+($_0_arg.$2.slice(1)));
        }
        
        return Backend__ReasonML__renderApp($_0_arg.$1, $cg$3, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Backend__ReasonML__renderType(), $_0_arg.$3));
    } else if(($_0_arg.type === 1)) {
        return Text__PrettyPrint__WL__Combinators__encloseSep(Text__PrettyPrint__WL__Core__char("("), Text__PrettyPrint__WL__Core__char(")"), Text__PrettyPrint__WL__Core__char(","), Data__Vect__foldrImpl(null, null, null, $partial_0_2$Backend__JSON___123_disjointSubSchema_95_29_125_(), $HC_0_0$Prelude__List__Nil, $partial_0_1$Typedefs___123_apN_95_20_125_(), Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Backend__ReasonML__renderType(), $_0_arg.$2)));
    } else if(($_0_arg.type === 0)) {
        return Text__PrettyPrint__WL__Core__text("unit");
    } else {
        return Text__PrettyPrint__WL__Core__text($_0_arg.$1);
    }
}

// Prelude.List.replicate

function Prelude__List__replicate($_0_arg, $_1_arg, $_2_arg){
    
    if($_1_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
        return $HC_0_0$Prelude__List__Nil;
    } else {
        const $_3_in = $_1_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
        return new $HC_2_1$Prelude__List___58__58_($_2_arg, Prelude__List__replicate(null, $_3_in, $_2_arg));
    }
}

// Prelude.List.reverseOnto

function Prelude__List__reverseOnto($_0_arg, $_1_arg, $_2_arg){
    for(;;) {
        
        if(($_2_arg.type === 1)) {
            $_0_arg = null;
            $_1_arg = new $HC_2_1$Prelude__List___58__58_($_2_arg.$1, $_1_arg);
            $_2_arg = $_2_arg.$2;
        } else {
            return $_1_arg;
        }
    }
}

// TParsec.Combinators.roptand

function TParsec__Combinators__roptand($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_arg){
    let $cg$1 = null;
    const $cg$3 = $_4_arg.$1;
    $cg$1 = $cg$3.$1;
    return $partial_8_11$TParsec__Combinators__map(null, null, null, null, $cg$1, $partial_0_1$TParsec__Combinators___123_rand_95_399_125_(), null, TParsec__Combinators__optand(null, null, null, null, $_4_arg, $_5_arg, null, $_7_arg, $_8_arg));
}

// Data.Fin.shift

function Data__Fin__shift($_0_arg, $_1_arg, $_2_arg){
    
    if($_1_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
        return $_2_arg;
    } else {
        const $_3_in = $_1_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
        return new $HC_1_1$Data__Fin__FS(Data__Fin__shift(null, $_3_in, $_2_arg));
    }
}

// Typedefs.shiftVars

function Typedefs__shiftVars($_0_arg, $_1_arg){
    
    if(($_1_arg.type === 0)) {
        return $_1_arg;
    } else if(($_1_arg.type === 1)) {
        return $_1_arg;
    } else if(($_1_arg.type === 6)) {
        return new $HC_3_6$Typedefs__TApp($_1_arg.$1, $_1_arg.$2, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_1_2$Typedefs__shiftVars(null), $_1_arg.$3));
    } else if(($_1_arg.type === 5)) {
        return new $HC_2_5$Typedefs__TMu($_1_arg.$1, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Typedefs___123_shiftVars_95_427_125_(), $_1_arg.$2));
    } else if(($_1_arg.type === 3)) {
        return new $HC_2_3$Typedefs__TProd($_1_arg.$1, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_1_2$Typedefs__shiftVars(null), $_1_arg.$2));
    } else if(($_1_arg.type === 2)) {
        return new $HC_2_2$Typedefs__TSum($_1_arg.$1, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_1_2$Typedefs__shiftVars(null), $_1_arg.$2));
    } else {
        return new $HC_1_4$Typedefs__TVar(Data__Fin__shift(null, (new $JSRTS.jsbn.BigInteger(("1"))), $_1_arg.$1));
    }
}

// Language.JSON.Data.showChar

function Language__JSON__Data__showChar($_0_arg){
    
    if(($_0_arg === "\b")) {
        return "\\b";
    } else if(($_0_arg === "\t")) {
        return "\\t";
    } else if(($_0_arg === "\n")) {
        return "\\n";
    } else if(($_0_arg === "\f")) {
        return "\\f";
    } else if(($_0_arg === "\r")) {
        return "\\r";
    } else if(($_0_arg === "\"")) {
        return "\\\"";
    } else if(($_0_arg === "\\")) {
        return "\\\\";
    } else {
        let $cg$2 = null;
        if(Prelude__Chars__isControl($_0_arg)) {
            $cg$2 = true;
        } else {
            
            if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Char_58__33_compare_58_0($_0_arg, "\x7f") > 0)) {
                $cg$2 = true;
            } else {
                $cg$2 = ($_0_arg === "\x7f");
            }
        }
        
        
        if($cg$2) {
            return ("\\u" + Prelude__Bits__b16ToHexString((((new $JSRTS.jsbn.BigInteger(''+((($_0_arg).charCodeAt(0)|0))))).intValue() & 0xFFFF)));
        } else {
            return (($_0_arg)+(""));
        }
    }
}

// Language.JSON.Data.showString

function Language__JSON__Data__showString($_0_arg){
    let $cg$1 = null;
    if((((($_0_arg == "")) ? 1|0 : 0|0) === 0)) {
        $cg$1 = true;
    } else {
        $cg$1 = false;
    }
    
    const $cg$3 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$1, true);
    let $cg$2 = null;
    if(($cg$3.type === 1)) {
        $cg$2 = $HC_0_0$Prelude__List__Nil;
    } else {
        let $cg$4 = null;
        if((((($_0_arg.slice(1) == "")) ? 1|0 : 0|0) === 0)) {
            $cg$4 = true;
        } else {
            $cg$4 = false;
        }
        
        const $cg$6 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$4, true);
        let $cg$5 = null;
        if(($cg$6.type === 1)) {
            $cg$5 = $HC_0_0$Prelude__Strings__StrNil;
        } else {
            $cg$5 = new $HC_2_1$Prelude__Strings__StrCons($_0_arg.slice(1)[0], $_0_arg.slice(1).slice(1));
        }
        
        $cg$2 = new $HC_2_1$Prelude__List___58__58_($_0_arg[0], _95_Prelude__Strings__unpack_95_with_95_36(null, $cg$5));
    }
    
    return ("\"" + (Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $partial_0_2$Language__JSON__Data___123_showString_95_428_125_(), "", $cg$2) + "\""));
}

// TParsec.Combinators.Chars.space

function TParsec__Combinators__Chars__space($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    const $cg$2 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0(true, true);
    let $cg$1 = null;
    if(($cg$2.type === 1)) {
        $cg$1 = $HC_0_0$Prelude__List__Nil;
    } else {
        let $cg$3 = null;
        if(((((" \t\n".slice(1) == "")) ? 1|0 : 0|0) === 0)) {
            $cg$3 = true;
        } else {
            $cg$3 = false;
        }
        
        const $cg$5 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$3, true);
        let $cg$4 = null;
        if(($cg$5.type === 1)) {
            $cg$4 = $HC_0_0$Prelude__Strings__StrNil;
        } else {
            $cg$4 = new $HC_2_1$Prelude__Strings__StrCons(" \t\n".slice(1)[0], " \t\n".slice(1).slice(1));
        }
        
        $cg$1 = new $HC_2_1$Prelude__List___58__58_(" \t\n"[0], _95_Prelude__Strings__unpack_95_with_95_36(null, $cg$4));
    }
    
    return TParsec__Combinators__anyOf(null, $_1_arg, $_2_arg, $_3_arg, $_6_arg, $_5_arg, Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $_4_arg, $cg$1), null);
}

// Text.PrettyPrint.WL.Core.spaces

function Text__PrettyPrint__WL__Core__spaces($_0_arg){
    let $cg$1 = null;
    if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Int_58__33_compare_58_0($_0_arg, 0) < 0)) {
        $cg$1 = true;
    } else {
        $cg$1 = ($_0_arg === 0);
    }
    
    
    if($cg$1) {
        return "";
    } else {
        return Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $partial_0_2$prim_95__95_strCons(), "", Prelude__List__replicate(null, (new $JSRTS.jsbn.BigInteger(''+($_0_arg))), " "));
    }
}

// TParsec.Combinators.Chars.string

function TParsec__Combinators__Chars__string($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_arg, $_9_arg){
    let $cg$1 = null;
    if((((($_7_arg == "")) ? 1|0 : 0|0) === 0)) {
        $cg$1 = true;
    } else {
        $cg$1 = false;
    }
    
    const $cg$3 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$1, true);
    if(($cg$3.type === 1)) {
        return null;
    } else {
        let $cg$4 = null;
        const $cg$6 = $_3_arg.$1;
        $cg$4 = $cg$6.$1;
        let $cg$7 = null;
        if((((($_7_arg.slice(1) == "")) ? 1|0 : 0|0) === 0)) {
            $cg$7 = true;
        } else {
            $cg$7 = false;
        }
        
        const $cg$9 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$7, true);
        let $cg$8 = null;
        if(($cg$9.type === 1)) {
            $cg$8 = $HC_0_0$Prelude__List__Nil;
        } else {
            let $cg$10 = null;
            if((((($_7_arg.slice(1).slice(1) == "")) ? 1|0 : 0|0) === 0)) {
                $cg$10 = true;
            } else {
                $cg$10 = false;
            }
            
            const $cg$12 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$10, true);
            let $cg$11 = null;
            if(($cg$12.type === 1)) {
                $cg$11 = $HC_0_0$Prelude__Strings__StrNil;
            } else {
                $cg$11 = new $HC_2_1$Prelude__Strings__StrCons($_7_arg.slice(1).slice(1)[0], $_7_arg.slice(1).slice(1).slice(1));
            }
            
            $cg$8 = new $HC_2_1$Prelude__List___58__58_($_7_arg.slice(1)[0], _95_Prelude__Strings__unpack_95_with_95_36(null, $cg$11));
        }
        
        return $partial_8_11$TParsec__Combinators__map(null, null, null, null, $cg$4, $partial_1_2$TParsec__Combinators__Numbers___123_decimalDigit_95_25_125_($_7_arg), null, TParsec__Combinators__ands(null, null, null, $_3_arg, null, new $HC_2_0$Data__NEList__MkNEList(TParsec__Combinators__Chars__char(null, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg[0])($_9_arg), Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $partial_7_8$TParsec__Combinators__Chars___123_string_95_430_125_($_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_9_arg), $cg$8))));
    }
}

// Language.JSON.Data.stringify

function Language__JSON__Data__stringify($_0_arg){
    
    if(($_0_arg.type === 4)) {
        return ("[" + (Language__JSON__Data__stringify_58_stringifyValues_58_4(null, $_0_arg.$1) + "]"));
    } else if(($_0_arg.type === 1)) {
        
        if($_0_arg.$1) {
            return "true";
        } else {
            return "false";
        }
    } else if(($_0_arg.type === 2)) {
        return Prelude__Show__primNumShow(null, $partial_0_1$prim_95__95_floatToStr(), $HC_0_0$Prelude__Show__Open, $_0_arg.$1);
    } else if(($_0_arg.type === 5)) {
        return ("{" + (Language__JSON__Data__stringify_58_stringifyProps_58_5(null, $_0_arg.$1) + "}"));
    } else {
        return Language__JSON__Data__showString($_0_arg.$1);
    }
}

// Parse.tdef

function Parse__tdef($_0_arg){
    return Induction__Nat__fix(null, $partial_0_2$Parse___123_tdef_95_3441_125_(), $_0_arg);
}

// Text.PrettyPrint.WL.Core.text

function Text__PrettyPrint__WL__Core__text($_0_arg){
    
    if(($_0_arg === "")) {
        return $HC_0_0$Text__PrettyPrint__WL__Core__Empty;
    } else {
        return new $HC_2_2$Text__PrettyPrint__WL__Core__Text((((new $JSRTS.jsbn.BigInteger(''+((($_0_arg).length))))).intValue()|0), $_0_arg);
    }
}

// Parse.tnamed

function Parse__tnamed($_0_arg){
    return Parse__ignorespaces(null, null, $partial_0_3$Parse___123_tdef_95_431_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $partial_0_1$Typedefs___123_apN_95_20_125_(), new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Parse___123_tdef_95_538_125_(), $partial_0_2$Parse___123_tdef_95_539_125_()), $partial_0_2$Parse___123_tdef_95_540_125_(), $_0_arg, TParsec__Combinators__randbindm(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), null, TParsec__Combinators__Chars__parens(null, null, $partial_0_3$Parse___123_tdef_95_431_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $partial_0_1$Typedefs___123_apN_95_20_125_(), new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Parse___123_tdef_95_538_125_(), $partial_0_2$Parse___123_tdef_95_539_125_()), $partial_0_2$Parse___123_tdef_95_540_125_(), $_0_arg, $partial_1_5$Parse___123_tnamed_95_4350_125_($_0_arg)), $partial_0_1$Parse___123_tnamed_95_4399_125_()));
}

// Parse.tnamedRec

function Parse__tnamedRec($_0_arg){
    return Induction__Nat__fix(null, $partial_0_2$Parse___123_tnamedRec_95_4510_125_(), $_0_arg);
}

// Prelude.Maybe.toMaybe

function Prelude__Maybe__toMaybe($_0_arg, $_1_arg, $_2_arg){
    
    if($_1_arg) {
        return new $HC_1_1$Prelude__Maybe__Just($JSRTS.force($_2_arg));
    } else {
        return $HC_0_0$Prelude__Maybe__Nothing;
    }
}

// Text.PrettyPrint.WL.Core.toString

function Text__PrettyPrint__WL__Core__toString($_0_arg, $_1_arg, $_2_arg){
    return Text__PrettyPrint__WL__Core__showPrettyDoc_58_showPrettyDocS_58_0(null, Text__PrettyPrint__WL__Core__render_58_best_58_0($_0_arg, $_1_arg, null, $_1_arg, 0, 0, $_2_arg, $partial_0_1$Text__PrettyPrint__WL__Core___123_toString_95_4511_125_()), "");
}

// Parse.toVMax

function Parse__toVMax($_0_arg, $_1_arg, $_2_arg){
    
    const $cg$3 = $_2_arg.$1;
    const $cg$5 = $_2_arg.$2;
    if(($cg$5.type === 1)) {
        const $cg$7 = Parse__toVMax(null, null, new $HC_2_1$Data__Vect___58__58_($cg$5.$1, $cg$5.$2));
        const $cg$9 = Prelude__Nat__isLTE($cg$3.$1, $cg$7.$1);
        if(($cg$9.type === 1)) {
            return new $HC_2_0$Builtins__MkDPair($cg$3.$1, new $HC_4_2$Parse__VMConsMore($cg$7.$1, $cg$3.$2, $cg$7.$2, Prelude__Nat__notLTImpliesGTE($cg$7.$1, $cg$3.$1, null)));
        } else {
            return new $HC_2_0$Builtins__MkDPair($cg$7.$1, new $HC_4_1$Parse__VMConsLess($cg$3.$1, $cg$3.$2, $cg$7.$2, $cg$9.$1));
        }
    } else {
        return new $HC_2_0$Builtins__MkDPair($cg$3.$1, new $HC_1_0$Parse__VMEnd($cg$3.$2));
    }
}

// Data.SortedMap.treeInsert

function Data__SortedMap__treeInsert($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg){
    const $cg$2 = Data__SortedMap__treeInsert_39_(null, null, $_2_arg, null, $_4_arg, $_5_arg, $_6_arg);
    if(($cg$2.type === 0)) {
        return new $HC_1_0$Prelude__Either__Left($cg$2.$1);
    } else {
        const $cg$4 = $cg$2.$1;
        const $cg$6 = $cg$4.$2;
        return new $HC_1_1$Prelude__Either__Right(new $HC_3_1$Data__SortedMap__Branch2($cg$4.$1, $cg$6.$1, $cg$6.$2));
    }
}

// Data.SortedMap.treeInsert'

function Data__SortedMap__treeInsert_39_($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg){
    
    if(($_6_arg.type === 1)) {
        
        
        if($_2_arg.$3($_4_arg)($_6_arg.$2)) {
            const $cg$36 = Data__SortedMap__treeInsert_39_(null, null, $_2_arg, null, $_4_arg, $_5_arg, $_6_arg.$1);
            if(($cg$36.type === 0)) {
                return new $HC_1_0$Prelude__Either__Left(new $HC_3_1$Data__SortedMap__Branch2($cg$36.$1, $_6_arg.$2, $_6_arg.$3));
            } else {
                const $cg$38 = $cg$36.$1;
                const $cg$40 = $cg$38.$2;
                return new $HC_1_0$Prelude__Either__Left(new $HC_5_2$Data__SortedMap__Branch3($cg$38.$1, $cg$40.$1, $cg$40.$2, $_6_arg.$2, $_6_arg.$3));
            }
        } else {
            const $cg$30 = Data__SortedMap__treeInsert_39_(null, null, $_2_arg, null, $_4_arg, $_5_arg, $_6_arg.$3);
            if(($cg$30.type === 0)) {
                return new $HC_1_0$Prelude__Either__Left(new $HC_3_1$Data__SortedMap__Branch2($_6_arg.$1, $_6_arg.$2, $cg$30.$1));
            } else {
                const $cg$32 = $cg$30.$1;
                const $cg$34 = $cg$32.$2;
                return new $HC_1_0$Prelude__Either__Left(new $HC_5_2$Data__SortedMap__Branch3($_6_arg.$1, $_6_arg.$2, $cg$32.$1, $cg$34.$1, $cg$34.$2));
            }
        }
    } else if(($_6_arg.type === 2)) {
        
        
        if($_2_arg.$3($_4_arg)($_6_arg.$2)) {
            const $cg$22 = Data__SortedMap__treeInsert_39_(null, null, $_2_arg, null, $_4_arg, $_5_arg, $_6_arg.$1);
            if(($cg$22.type === 0)) {
                return new $HC_1_0$Prelude__Either__Left(new $HC_5_2$Data__SortedMap__Branch3($cg$22.$1, $_6_arg.$2, $_6_arg.$3, $_6_arg.$4, $_6_arg.$5));
            } else {
                const $cg$24 = $cg$22.$1;
                const $cg$26 = $cg$24.$2;
                return new $HC_1_1$Prelude__Either__Right(new $HC_2_0$Builtins__MkPair(new $HC_3_1$Data__SortedMap__Branch2($cg$24.$1, $cg$26.$1, $cg$26.$2), new $HC_2_0$Builtins__MkPair($_6_arg.$2, new $HC_3_1$Data__SortedMap__Branch2($_6_arg.$3, $_6_arg.$4, $_6_arg.$5))));
            }
        } else {
            
            
            if($_2_arg.$3($_4_arg)($_6_arg.$4)) {
                const $cg$16 = Data__SortedMap__treeInsert_39_(null, null, $_2_arg, null, $_4_arg, $_5_arg, $_6_arg.$3);
                if(($cg$16.type === 0)) {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_5_2$Data__SortedMap__Branch3($_6_arg.$1, $_6_arg.$2, $cg$16.$1, $_6_arg.$4, $_6_arg.$5));
                } else {
                    const $cg$18 = $cg$16.$1;
                    const $cg$20 = $cg$18.$2;
                    return new $HC_1_1$Prelude__Either__Right(new $HC_2_0$Builtins__MkPair(new $HC_3_1$Data__SortedMap__Branch2($_6_arg.$1, $_6_arg.$2, $cg$18.$1), new $HC_2_0$Builtins__MkPair($cg$20.$1, new $HC_3_1$Data__SortedMap__Branch2($cg$20.$2, $_6_arg.$4, $_6_arg.$5))));
                }
            } else {
                const $cg$10 = Data__SortedMap__treeInsert_39_(null, null, $_2_arg, null, $_4_arg, $_5_arg, $_6_arg.$5);
                if(($cg$10.type === 0)) {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_5_2$Data__SortedMap__Branch3($_6_arg.$1, $_6_arg.$2, $_6_arg.$3, $_6_arg.$4, $cg$10.$1));
                } else {
                    const $cg$12 = $cg$10.$1;
                    const $cg$14 = $cg$12.$2;
                    return new $HC_1_1$Prelude__Either__Right(new $HC_2_0$Builtins__MkPair(new $HC_3_1$Data__SortedMap__Branch2($_6_arg.$1, $_6_arg.$2, $_6_arg.$3), new $HC_2_0$Builtins__MkPair($_6_arg.$4, new $HC_3_1$Data__SortedMap__Branch2($cg$12.$1, $cg$14.$1, $cg$14.$2))));
                }
            }
        }
    } else {
        
        const $cg$4 = $_2_arg.$2($_4_arg)($_6_arg.$1);
        if(($cg$4 === 0)) {
            return new $HC_1_0$Prelude__Either__Left(new $HC_2_0$Data__SortedMap__Leaf($_4_arg, $_5_arg));
        } else if(($cg$4 > 0)) {
            return new $HC_1_1$Prelude__Either__Right(new $HC_2_0$Builtins__MkPair(new $HC_2_0$Data__SortedMap__Leaf($_6_arg.$1, $_6_arg.$2), new $HC_2_0$Builtins__MkPair($_6_arg.$1, new $HC_2_0$Data__SortedMap__Leaf($_4_arg, $_5_arg))));
        } else {
            return new $HC_1_1$Prelude__Either__Right(new $HC_2_0$Builtins__MkPair(new $HC_2_0$Data__SortedMap__Leaf($_4_arg, $_5_arg), new $HC_2_0$Builtins__MkPair($_4_arg, new $HC_2_0$Data__SortedMap__Leaf($_6_arg.$1, $_6_arg.$2))));
        }
    }
}

// Data.SortedMap.treeLookup

function Data__SortedMap__treeLookup($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg){
    for(;;) {
        
        if(($_5_arg.type === 1)) {
            
            
            if($_2_arg.$3($_4_arg)($_5_arg.$2)) {
                $_0_arg = null;
                $_1_arg = null;
                $_2_arg = $_2_arg;
                $_3_arg = null;
                $_4_arg = $_4_arg;
                $_5_arg = $_5_arg.$1;
            } else {
                $_0_arg = null;
                $_1_arg = null;
                $_2_arg = $_2_arg;
                $_3_arg = null;
                $_4_arg = $_4_arg;
                $_5_arg = $_5_arg.$3;
            }
        } else if(($_5_arg.type === 2)) {
            
            
            if($_2_arg.$3($_4_arg)($_5_arg.$2)) {
                $_0_arg = null;
                $_1_arg = null;
                $_2_arg = $_2_arg;
                $_3_arg = null;
                $_4_arg = $_4_arg;
                $_5_arg = $_5_arg.$1;
            } else {
                
                
                if($_2_arg.$3($_4_arg)($_5_arg.$4)) {
                    $_0_arg = null;
                    $_1_arg = null;
                    $_2_arg = $_2_arg;
                    $_3_arg = null;
                    $_4_arg = $_4_arg;
                    $_5_arg = $_5_arg.$3;
                } else {
                    $_0_arg = null;
                    $_1_arg = null;
                    $_2_arg = $_2_arg;
                    $_3_arg = null;
                    $_4_arg = $_4_arg;
                    $_5_arg = $_5_arg.$5;
                }
            }
        } else {
            
            const $cg$4 = $_2_arg.$1;
            
            if($cg$4.$1($_4_arg)($_5_arg.$1)) {
                return new $HC_1_1$Prelude__Maybe__Just($_5_arg.$2);
            } else {
                return $HC_0_0$Prelude__Maybe__Nothing;
            }
        }
    }
}

// TParsec.Combinators.Chars.upperAlpha

function TParsec__Combinators__Chars__upperAlpha($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    const $cg$2 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0(true, true);
    let $cg$1 = null;
    if(($cg$2.type === 1)) {
        $cg$1 = $HC_0_0$Prelude__List__Nil;
    } else {
        let $cg$3 = null;
        if((((("ABCDEFGHIJKLMNOPQRSTUVWXYZ".slice(1) == "")) ? 1|0 : 0|0) === 0)) {
            $cg$3 = true;
        } else {
            $cg$3 = false;
        }
        
        const $cg$5 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$3, true);
        let $cg$4 = null;
        if(($cg$5.type === 1)) {
            $cg$4 = $HC_0_0$Prelude__Strings__StrNil;
        } else {
            $cg$4 = new $HC_2_1$Prelude__Strings__StrCons("ABCDEFGHIJKLMNOPQRSTUVWXYZ".slice(1)[0], "ABCDEFGHIJKLMNOPQRSTUVWXYZ".slice(1).slice(1));
        }
        
        $cg$1 = new $HC_2_1$Prelude__List___58__58_("ABCDEFGHIJKLMNOPQRSTUVWXYZ"[0], _95_Prelude__Strings__unpack_95_with_95_36(null, $cg$4));
    }
    
    return TParsec__Combinators__anyOf(null, $_1_arg, $_2_arg, $_3_arg, $_6_arg, $_5_arg, Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $_4_arg, $cg$1), null);
}

// Data.Fin.weakenN

function Data__Fin__weakenN($_0_arg, $_1_arg, $_2_arg){
    
    if(($_2_arg.type === 1)) {
        return new $HC_1_1$Data__Fin__FS(Data__Fin__weakenN(null, null, $_2_arg.$1));
    } else {
        return $_2_arg;
    }
}

// Typedefs.weakenNTDefs

function Typedefs__weakenNTDefs($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    
    if(($_2_arg.type === 1)) {
        const $cg$3 = $_2_arg.$1;
        return new $HC_2_1$Data__Vect___58__58_(new $HC_2_0$Builtins__MkPair($cg$3.$1, Typedefs__weakenTDef(null, $cg$3.$2, $_3_arg, $_4_arg)), Typedefs__weakenNTDefs(null, null, $_2_arg.$2, $_3_arg, $_4_arg));
    } else {
        return $_2_arg;
    }
}

// Typedefs.weakenTDef

function Typedefs__weakenTDef($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    if(($_1_arg.type === 0)) {
        return $_1_arg;
    } else if(($_1_arg.type === 1)) {
        return $_1_arg;
    } else if(($_1_arg.type === 6)) {
        return new $HC_3_6$Typedefs__TApp($_1_arg.$1, $_1_arg.$2, Typedefs__weakenTDefs(null, null, $_1_arg.$3, $_2_arg, $_3_arg));
    } else if(($_1_arg.type === 5)) {
        return new $HC_2_5$Typedefs__TMu($_1_arg.$1, Typedefs__weakenNTDefs(null, null, $_1_arg.$2, $_2_arg.add((new $JSRTS.jsbn.BigInteger(("1")))), new $HC_1_1$Prelude__Nat__LTESucc($_3_arg)));
    } else if(($_1_arg.type === 3)) {
        return new $HC_2_3$Typedefs__TProd($_1_arg.$1, Typedefs__weakenTDefs(null, null, $_1_arg.$2, $_2_arg, $_3_arg));
    } else if(($_1_arg.type === 2)) {
        return new $HC_2_2$Typedefs__TSum($_1_arg.$1, Typedefs__weakenTDefs(null, null, $_1_arg.$2, $_2_arg, $_3_arg));
    } else {
        
        if($_2_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
            return null;
        } else {
            const $_14_in = $_2_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
            let $_15_in = null;
            $_15_in = $_3_arg.$1;
            return new $HC_1_4$Typedefs__TVar(Data__Fin__weakenN(null, null, $_1_arg.$1));
        }
    }
}

// Typedefs.weakenTDefs

function Typedefs__weakenTDefs($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    
    if(($_2_arg.type === 1)) {
        return new $HC_2_1$Data__Vect___58__58_(Typedefs__weakenTDef(null, $_2_arg.$1, $_3_arg, $_4_arg), Typedefs__weakenTDefs(null, null, $_2_arg.$2, $_3_arg, $_4_arg));
    } else {
        return $_2_arg;
    }
}

// TParsec.Combinators.Chars.withSpaces

function TParsec__Combinators__Chars__withSpaces($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_arg, $_9_arg){
    return TParsec__Combinators__roptand(null, null, null, null, $_4_arg, $_3_arg, null, TParsec__Combinators__nelist(null, null, null, $_3_arg, $_4_arg, $_8_arg)(TParsec__Combinators__Chars__space(null, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, null)), TParsec__Combinators__landopt(null, null, null, null, $_4_arg, $_3_arg, null, $_9_arg, $partial_7_11$TParsec__Combinators__Chars___123_withSpaces_95_4512_125_($_3_arg, $_4_arg, $_8_arg, $_2_arg, $_5_arg, $_6_arg, $_7_arg)));
}

// Prelude.List.zipWith

function Prelude__List__zipWith($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg){
    
    if(($_5_arg.type === 1)) {
        
        if(($_4_arg.type === 1)) {
            return new $HC_2_1$Prelude__List___58__58_($_3_arg($_4_arg.$1)($_5_arg.$1), Prelude__List__zipWith(null, null, null, $_3_arg, $_4_arg.$2, $_5_arg.$2));
        } else {
            return $_4_arg;
        }
    } else {
        
        if(($_4_arg.type === 1)) {
            return $HC_0_0$Prelude__List__Nil;
        } else {
            return $_4_arg;
        }
    }
}

// Data.Vect.zipWith

function Data__Vect__zipWith($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg){
    
    if(($_6_arg.type === 1)) {
        
        return new $HC_2_1$Data__Vect___58__58_($_4_arg($_5_arg.$1)($_6_arg.$1), Data__Vect__zipWith(null, null, null, null, $_4_arg, $_5_arg.$2, $_6_arg.$2));
    } else {
        return $_6_arg;
    }
}

// TParsec.Combinators.Chars.{alphas_0}

function TParsec__Combinators__Chars___123_alphas_95_0_125_($_0_lift, $_1_lift){
    let $cg$1 = null;
    $cg$1 = $_1_lift.$1;
    let $cg$2 = null;
    $cg$2 = $_1_lift.$2;
    return Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $partial_0_2$prim_95__95_strCons(), "", Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $_0_lift, new $HC_2_1$Prelude__List___58__58_($cg$1, $cg$2)));
}

// TParsec.Combinators.{alts_1}

function TParsec__Combinators___123_alts_95_1_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    
    return $_0_lift.$2(null);
}

// TParsec.Combinators.{andbind_2}

function TParsec__Combinators___123_andbind_95_2_125_($_0_lift, $_1_lift, $_2_lift){
    
    const $cg$3 = $_0_lift.$1;
    let $cg$4 = null;
    $cg$4 = $_2_lift.$1;
    let $cg$5 = null;
    $cg$5 = $_2_lift.$2;
    let $cg$6 = null;
    $cg$6 = $_2_lift.$3;
    let $cg$7 = null;
    $cg$7 = $_2_lift.$2;
    let $cg$8 = null;
    $cg$8 = $_2_lift.$2;
    let $cg$9 = null;
    $cg$9 = $_2_lift.$4;
    return $cg$3.$1(null)(null)($partial_5_6$TParsec__Success__and(null, null, null, null, $_2_lift))($_1_lift($cg$4)($cg$5)(Prelude__Nat__lteTransitive(null, null, null, $cg$6, null))($cg$7)(Prelude__Nat__lteRefl($cg$8))($cg$9));
}

// TParsec.Combinators.{andbindm_3}

function TParsec__Combinators___123_andbindm_95_3_125_($_0_lift, $_1_lift, $_2_lift){
    
    const $cg$3 = $_0_lift.$1;
    let $cg$4 = null;
    $cg$4 = new $HC_4_0$TParsec__Success__MkSuccess(new $HC_2_0$Builtins__MkPair($_1_lift.$1, $_2_lift), $_1_lift.$2, $_1_lift.$3, $_1_lift.$4);
    return $cg$3.$2(null)($cg$4);
}

// TParsec.Combinators.{andbindm_4}

function TParsec__Combinators___123_andbindm_95_4_125_($_0_lift, $_1_lift, $_2_lift){
    
    let $cg$2 = null;
    $cg$2 = $_2_lift.$1;
    return $_0_lift.$2(null)(null)($_1_lift($cg$2))($partial_2_3$TParsec__Combinators___123_andbindm_95_3_125_($_0_lift, $_2_lift));
}

// TParsec.Combinators.{andoptbind_5}

function TParsec__Combinators___123_andoptbind_95_5_125_($_0_lift, $_1_lift){
    const $cg$2 = TParsec__Success__and(null, null, null, null, $_0_lift, $_1_lift);
    const $cg$4 = $cg$2.$1;
    let $cg$3 = null;
    $cg$3 = new $HC_2_0$Builtins__MkPair($cg$4.$1, new $HC_1_1$Prelude__Maybe__Just($cg$4.$2));
    return new $HC_4_0$TParsec__Success__MkSuccess($cg$3, $cg$2.$2, $cg$2.$3, $cg$2.$4);
}

// TParsec.Combinators.{andoptbind_6}

function TParsec__Combinators___123_andoptbind_95_6_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    
    let $cg$2 = null;
    const $cg$4 = $_1_lift.$1;
    let $cg$5 = null;
    $cg$5 = $_3_lift.$1;
    let $cg$6 = null;
    $cg$6 = $_3_lift.$2;
    let $cg$7 = null;
    $cg$7 = $_3_lift.$3;
    let $cg$8 = null;
    $cg$8 = $_3_lift.$2;
    let $cg$9 = null;
    $cg$9 = $_3_lift.$2;
    let $cg$10 = null;
    $cg$10 = $_3_lift.$4;
    $cg$2 = $cg$4.$1(null)(null)($partial_1_2$TParsec__Combinators___123_andoptbind_95_5_125_($_3_lift))($_2_lift($cg$5)($cg$6)(Prelude__Nat__lteTransitive(null, null, null, $cg$7, null))($cg$8)(Prelude__Nat__lteRefl($cg$9))($cg$10));
    let $cg$11 = null;
    const $cg$13 = $_1_lift.$1;
    let $cg$14 = null;
    $cg$14 = new $HC_4_0$TParsec__Success__MkSuccess(new $HC_2_0$Builtins__MkPair($_3_lift.$1, $HC_0_0$Prelude__Maybe__Nothing), $_3_lift.$2, $_3_lift.$3, $_3_lift.$4);
    $cg$11 = $cg$13.$2(null)($cg$14);
    return $_0_lift.$3(null)($cg$2)($cg$11);
}

// TParsec.Combinators.{ands_7}

function TParsec__Combinators___123_ands_95_7_125_($_0_lift){
    
    const $cg$3 = $_0_lift.$1;
    const $cg$5 = $_0_lift.$2;
    let $cg$4 = null;
    $cg$4 = $cg$5.$1;
    const $cg$7 = $_0_lift.$2;
    let $cg$6 = null;
    $cg$6 = $cg$7.$2;
    return new $HC_2_0$Data__NEList__MkNEList($cg$3.$1, Prelude__List___43__43_(null, $cg$3.$2, new $HC_2_1$Prelude__List___58__58_($cg$4, $cg$6)));
}

// TParsec.Combinators.{ands_8}

function TParsec__Combinators___123_ands_95_8_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift){
    return $_0_lift($_4_lift)(Prelude__Nat__lteTransitive(null, null, null, $_5_lift, null));
}

// TParsec.Combinators.{ands_9}

function TParsec__Combinators___123_ands_95_9_125_($_0_lift, $_1_lift, $_2_lift){
    let $cg$1 = null;
    const $cg$3 = $_0_lift.$1;
    $cg$1 = $cg$3.$1;
    return $partial_8_11$TParsec__Combinators__map(null, null, null, null, $cg$1, $partial_0_1$TParsec__Combinators___123_ands_95_7_125_(), null, $partial_8_11$TParsec__Combinators__andbind(null, null, null, null, $_0_lift, null, $_1_lift, $partial_1_6$TParsec__Combinators___123_ands_95_8_125_($_2_lift)));
}

// TParsec.Combinators.{ands_10}

function TParsec__Combinators___123_ands_95_10_125_($_0_lift){
    return new $HC_2_0$Data__NEList__MkNEList($_0_lift, $HC_0_0$Prelude__List__Nil);
}

// TParsec.Combinators.{anyOf_12}

function TParsec__Combinators___123_anyOf_95_12_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift){
    return TParsec__Combinators__exact(null, $_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, null);
}

// TParsec.Combinators.{anyTok_13}

function TParsec__Combinators___123_anyTok_95_13_125_($_0_lift, $_1_lift){
    return $_1_lift;
}

// TParsec.Combinators.{anyTok_14}

function TParsec__Combinators___123_anyTok_95_14_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    
    let $cg$2 = null;
    const $cg$4 = $_0_lift.$1;
    let $cg$5 = null;
    const $cg$7 = $_0_lift.$1;
    let $cg$8 = null;
    $cg$8 = $_2_lift.$1;
    $cg$5 = $cg$7.$1(null)(null)($partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_())($_1_lift($cg$8));
    let $cg$9 = null;
    const $cg$11 = $_0_lift.$1;
    $cg$9 = $cg$11.$2(null)($_2_lift);
    $cg$2 = $cg$4.$3(null)(null)($cg$5)($cg$9);
    return $_0_lift.$3(null)($cg$2)($_3_lift);
}

// Typedefs.{ap_15}

function Typedefs___123_ap_95_15_125_($_0_lift, $_1_lift, $_2_lift){
    return Typedefs__ap($_0_lift, null, $_2_lift, $_1_lift);
}

// Typedefs.{ap_16}

function Typedefs___123_ap_95_16_125_($_0_lift, $_1_lift, $_2_lift){
    
    const $cg$3 = Data__Fin__integerToFin((new $JSRTS.jsbn.BigInteger(("0"))), $_0_lift.add((new $JSRTS.jsbn.BigInteger(("1")))));
    let $cg$2 = null;
    $cg$2 = $cg$3.$1;
    return new $HC_2_0$Builtins__MkPair($_2_lift.$1, Typedefs__ap($_0_lift.add((new $JSRTS.jsbn.BigInteger(("1")))), null, $_2_lift.$2, new $HC_2_1$Data__Vect___58__58_(new $HC_1_4$Typedefs__TVar($cg$2), Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_1_2$Typedefs__shiftVars(null), $_1_lift))));
}

// Typedefs.{apN_19}

function Typedefs___123_apN_95_19_125_($_0_lift, $_1_lift){
    return ($_0_lift + $_1_lift);
}

// Typedefs.{apN_20}

function Typedefs___123_apN_95_20_125_($_0_lift){
    return $_0_lift;
}

// Prelude.Bits.{b16ToHexString_23}

function Prelude__Bits___123_b16ToHexString_95_23_125_($_0_lift, $_1_lift){
    return (Prelude__Bits__b8ToHexString($_0_lift) + $_1_lift);
}

// Data.NEList.{consopt_24}

function Data__NEList___123_consopt_95_24_125_($_0_lift){
    let $cg$1 = null;
    $cg$1 = $_0_lift.$1;
    let $cg$2 = null;
    $cg$2 = $_0_lift.$2;
    return new $HC_2_1$Prelude__List___58__58_($cg$1, $cg$2);
}

// TParsec.Combinators.Numbers.{decimalDigit_25}

function TParsec__Combinators__Numbers___123_decimalDigit_95_25_125_($_0_lift, $_1_lift){
    return $_0_lift;
}

// TParsec.Combinators.Numbers.{decimalDigit_26}

function TParsec__Combinators__Numbers___123_decimalDigit_95_26_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift){
    
    let $cg$2 = null;
    const $cg$4 = $_0_lift.$1;
    $cg$2 = $cg$4.$1;
    return $partial_8_11$TParsec__Combinators__map(null, null, null, null, $cg$2, $partial_1_2$TParsec__Combinators__Numbers___123_decimalDigit_95_25_125_($_6_lift.$1), null, TParsec__Combinators__exact(null, $_1_lift, $_2_lift, $_0_lift, $_3_lift, $_4_lift, $_5_lift($_6_lift.$2), null));
}

// TParsec.Combinators.Numbers.{decimalNat_27}

function TParsec__Combinators__Numbers___123_decimalNat_95_27_125_($_0_lift, $_1_lift){
    return (new $JSRTS.jsbn.BigInteger(("10"))).multiply($_0_lift).add($_1_lift);
}

// TParsec.Combinators.Numbers.{decimalNat_28}

function TParsec__Combinators__Numbers___123_decimalNat_95_28_125_($_0_lift){
    let $cg$1 = null;
    $cg$1 = $_0_lift.$1;
    let $cg$2 = null;
    $cg$2 = $_0_lift.$2;
    return Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldl_58_0(null, null, $partial_0_2$TParsec__Combinators__Numbers___123_decimalNat_95_27_125_(), (new $JSRTS.jsbn.BigInteger(("0"))), new $HC_2_1$Prelude__List___58__58_($cg$1, $cg$2));
}

// Backend.JSON.{disjointSubSchema_29}

function Backend__JSON___123_disjointSubSchema_95_29_125_($_0_lift, $_1_lift){
    return new $HC_2_1$Prelude__List___58__58_($_0_lift, $_1_lift);
}

// Parse.{emptyComments_33}

function Parse___123_emptyComments_95_33_125_($_0_lift){
    return $HC_0_0$MkUnit;
}

// Text.PrettyPrint.WL.Combinators.{encloseSep_34}

function Text__PrettyPrint__WL__Combinators___123_encloseSep_95_34_125_($_0_lift, $_1_lift){
    return Text__PrettyPrint__WL__Core__flatten($_0_lift($_1_lift));
}

// Text.PrettyPrint.WL.Combinators.{encloseSep_36}

function Text__PrettyPrint__WL__Combinators___123_encloseSep_95_36_125_($_0_lift, $_1_lift){
    return new $HC_2_4$Text__PrettyPrint__WL__Core__Cat($_0_lift, new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(new $HC_1_3$Text__PrettyPrint__WL__Core__Line(true), $_1_lift));
}

// Text.PrettyPrint.WL.Combinators.{encloseSep_37}

function Text__PrettyPrint__WL__Combinators___123_encloseSep_95_37_125_($_0_lift, $_1_lift){
    return new $HC_2_4$Text__PrettyPrint__WL__Core__Cat($_0_lift, $_1_lift);
}

// Text.PrettyPrint.WL.Combinators.{encloseSep_42}

function Text__PrettyPrint__WL__Combinators___123_encloseSep_95_42_125_($_0_lift, $_1_lift, $_2_lift){
    const $cg$2 = Prelude__List__zipWith(null, null, null, $partial_0_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_37_125_(), new $HC_2_1$Prelude__List___58__58_($_0_lift, Prelude__List__replicate(null, Prelude__List__length(null, $_1_lift), $_2_lift)), $_1_lift);
    if(($cg$2.type === 1)) {
        return Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldl_58_0(null, null, $partial_0_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_36_125_(), $cg$2.$1, $cg$2.$2);
    } else {
        return $HC_0_0$Text__PrettyPrint__WL__Core__Empty;
    }
}

// Text.PrettyPrint.WL.Combinators.{encloseSep_43}

function Text__PrettyPrint__WL__Combinators___123_encloseSep_95_43_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift){
    const $cg$2 = Prelude__List__zipWith(null, null, null, $partial_0_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_37_125_(), new $HC_2_1$Prelude__List___58__58_($_1_lift, Prelude__List__replicate(null, Prelude__List__length(null, $_2_lift), $_3_lift)), $_2_lift);
    let $cg$1 = null;
    if(($cg$2.type === 1)) {
        $cg$1 = Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldl_58_0(null, null, $partial_0_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_36_125_(), $cg$2.$1, $cg$2.$2);
    } else {
        $cg$1 = $HC_0_0$Text__PrettyPrint__WL__Core__Empty;
    }
    
    let $cg$3 = null;
    if(($cg$1.type === 4)) {
        $cg$3 = new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__flatten($cg$1.$1), Text__PrettyPrint__WL__Core__flatten($cg$1.$2));
    } else if(($cg$1.type === 7)) {
        $cg$3 = new $HC_1_7$Text__PrettyPrint__WL__Core__Column($partial_1_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_34_125_($cg$1.$1));
    } else if(($cg$1.type === 3)) {
        
        if($cg$1.$1) {
            $cg$3 = $HC_0_0$Text__PrettyPrint__WL__Core__Empty;
        } else {
            $cg$3 = new $HC_2_2$Text__PrettyPrint__WL__Core__Text(1, " ");
        }
    } else if(($cg$1.type === 5)) {
        $cg$3 = new $HC_2_5$Text__PrettyPrint__WL__Core__Nest($cg$1.$1, Text__PrettyPrint__WL__Core__flatten($cg$1.$2));
    } else if(($cg$1.type === 8)) {
        $cg$3 = new $HC_1_8$Text__PrettyPrint__WL__Core__Nesting($partial_1_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_34_125_($cg$1.$1));
    } else if(($cg$1.type === 6)) {
        $cg$3 = Text__PrettyPrint__WL__Core__flatten($cg$1.$1);
    } else {
        const $cg$5 = Prelude__List__zipWith(null, null, null, $partial_0_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_37_125_(), new $HC_2_1$Prelude__List___58__58_($_1_lift, Prelude__List__replicate(null, Prelude__List__length(null, $_2_lift), $_3_lift)), $_2_lift);
        if(($cg$5.type === 1)) {
            $cg$3 = Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldl_58_0(null, null, $partial_0_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_36_125_(), $cg$5.$1, $cg$5.$2);
        } else {
            $cg$3 = $HC_0_0$Text__PrettyPrint__WL__Core__Empty;
        }
    }
    
    return new $HC_2_5$Text__PrettyPrint__WL__Core__Nest(($_0_lift - $_5_lift), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(new $HC_2_6$Text__PrettyPrint__WL__Core__Union($cg$3, new $JSRTS.Lazy((function(){
        return (function(){
            return Text__PrettyPrint__WL__Combinators___123_encloseSep_95_42_125_($_1_lift, $_2_lift, $_3_lift);
        })();
    }))), $_4_lift));
}

// Text.PrettyPrint.WL.Combinators.{encloseSep_44}

function Text__PrettyPrint__WL__Combinators___123_encloseSep_95_44_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    return new $HC_1_8$Text__PrettyPrint__WL__Core__Nesting($partial_5_6$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_43_125_($_4_lift, $_0_lift, $_1_lift, $_2_lift, $_3_lift));
}

// Text.PrettyPrint.WL.Combinators.{encloseSep_53}

function Text__PrettyPrint__WL__Combinators___123_encloseSep_95_53_125_($_0_lift, $_1_lift, $_2_lift){
    const $cg$2 = Prelude__List__zipWith(null, null, null, $partial_0_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_37_125_(), new $HC_2_1$Prelude__List___58__58_($_0_lift, Prelude__List__replicate(null, Prelude__List__length(null, $_1_lift), $_2_lift)), $_1_lift);
    if(($cg$2.type === 1)) {
        return Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldl_58_0(null, null, $partial_0_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_36_125_(), $cg$2.$1, $cg$2.$2);
    } else {
        return $HC_0_0$Text__PrettyPrint__WL__Core__Empty;
    }
}

// Text.PrettyPrint.WL.Combinators.{encloseSep_54}

function Text__PrettyPrint__WL__Combinators___123_encloseSep_95_54_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift){
    const $cg$2 = Prelude__List__zipWith(null, null, null, $partial_0_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_37_125_(), new $HC_2_1$Prelude__List___58__58_($_1_lift, Prelude__List__replicate(null, Prelude__List__length(null, $_2_lift), $_3_lift)), $_2_lift);
    let $cg$1 = null;
    if(($cg$2.type === 1)) {
        $cg$1 = Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldl_58_0(null, null, $partial_0_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_36_125_(), $cg$2.$1, $cg$2.$2);
    } else {
        $cg$1 = $HC_0_0$Text__PrettyPrint__WL__Core__Empty;
    }
    
    let $cg$3 = null;
    if(($cg$1.type === 4)) {
        $cg$3 = new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__flatten($cg$1.$1), Text__PrettyPrint__WL__Core__flatten($cg$1.$2));
    } else if(($cg$1.type === 7)) {
        $cg$3 = new $HC_1_7$Text__PrettyPrint__WL__Core__Column($partial_1_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_34_125_($cg$1.$1));
    } else if(($cg$1.type === 3)) {
        
        if($cg$1.$1) {
            $cg$3 = $HC_0_0$Text__PrettyPrint__WL__Core__Empty;
        } else {
            $cg$3 = new $HC_2_2$Text__PrettyPrint__WL__Core__Text(1, " ");
        }
    } else if(($cg$1.type === 5)) {
        $cg$3 = new $HC_2_5$Text__PrettyPrint__WL__Core__Nest($cg$1.$1, Text__PrettyPrint__WL__Core__flatten($cg$1.$2));
    } else if(($cg$1.type === 8)) {
        $cg$3 = new $HC_1_8$Text__PrettyPrint__WL__Core__Nesting($partial_1_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_34_125_($cg$1.$1));
    } else if(($cg$1.type === 6)) {
        $cg$3 = Text__PrettyPrint__WL__Core__flatten($cg$1.$1);
    } else {
        const $cg$5 = Prelude__List__zipWith(null, null, null, $partial_0_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_37_125_(), new $HC_2_1$Prelude__List___58__58_($_1_lift, Prelude__List__replicate(null, Prelude__List__length(null, $_2_lift), $_3_lift)), $_2_lift);
        if(($cg$5.type === 1)) {
            $cg$3 = Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldl_58_0(null, null, $partial_0_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_36_125_(), $cg$5.$1, $cg$5.$2);
        } else {
            $cg$3 = $HC_0_0$Text__PrettyPrint__WL__Core__Empty;
        }
    }
    
    return new $HC_2_5$Text__PrettyPrint__WL__Core__Nest(($_0_lift - $_5_lift), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(new $HC_2_6$Text__PrettyPrint__WL__Core__Union($cg$3, new $JSRTS.Lazy((function(){
        return (function(){
            return Text__PrettyPrint__WL__Combinators___123_encloseSep_95_53_125_($_1_lift, $_2_lift, $_3_lift);
        })();
    }))), $_4_lift));
}

// Text.PrettyPrint.WL.Combinators.{encloseSep_55}

function Text__PrettyPrint__WL__Combinators___123_encloseSep_95_55_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    return new $HC_1_8$Text__PrettyPrint__WL__Core__Nesting($partial_5_6$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_54_125_($_4_lift, $_0_lift, $_1_lift, $_2_lift, $_3_lift));
}

// TParsec.Combinators.{exact_57}

function TParsec__Combinators___123_exact_95_57_125_($_0_lift, $_1_lift, $_2_lift){
    let $cg$1 = null;
    $cg$1 = $_0_lift.$1($_1_lift)($_2_lift);
    return Prelude__Maybe__toMaybe(null, $cg$1, new $JSRTS.Lazy((function(){
        return (function(){
            return Typedefs___123_apN_95_20_125_($_2_lift);
        })();
    })));
}

// ParserUtils.{except_59}

function ParserUtils___123_except_95_59_125_($_0_lift, $_1_lift, $_2_lift){
    let $cg$1 = null;
    $cg$1 = $_0_lift.$2($_1_lift)($_2_lift);
    return Prelude__Maybe__toMaybe(null, $cg$1, new $JSRTS.Lazy((function(){
        return (function(){
            return Typedefs___123_apN_95_20_125_($_2_lift);
        })();
    })));
}

// Data.Vect.{foldrImpl_62}

function Data__Vect___123_foldrImpl_95_62_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return $_0_lift($_1_lift($_2_lift)($_3_lift));
}

// Backend.Utils.{freshEnv_63}

function Backend__Utils___123_freshEnv_95_63_125_($_0_lift, $_1_lift){
    return new $HC_1_0$Prelude__Either__Left(($_0_lift + Prelude__Show__primNumShow(null, $partial_0_1$prim_95__95_toStrBigInt(), $HC_0_0$Prelude__Show__Open, Data__Fin__finToInteger(null, $_1_lift))));
}

// Main.{generateCode_64}

function Main___123_generateCode_95_64_125_($_0_lift, $_1_lift){
    return Prelude__List__reverseOnto(null, $HC_0_0$Prelude__List__Nil, Control__Monad__State__evalState(null, null, Backend__Haskell__makeDefs_39_($_0_lift, $_1_lift), $HC_0_0$Prelude__List__Nil));
}

// Main.{generateCode_65}

function Main___123_generateCode_95_65_125_($_0_lift, $_1_lift){
    return Prelude__List__reverseOnto(null, $HC_0_0$Prelude__List__Nil, Control__Monad__State__evalState(null, null, Backend__ReasonML__makeDefs_39_($_0_lift, $_1_lift), $HC_0_0$Prelude__List__Nil));
}

// Backend.{generateDefs_66}

function Backend___123_generateDefs_95_66_125_($_0_lift, $_1_lift){
    return new $HC_2_4$Text__PrettyPrint__WL__Core__Cat($_0_lift, new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(new $HC_1_3$Text__PrettyPrint__WL__Core__Line(false), $_1_lift));
}

// TParsec.Success.{getTok_67}

function TParsec__Success___123_getTok_95_67_125_($_0_lift, $_1_lift){
    
    if($_0_lift.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
        return null;
    } else {
        const $_6_in = $_0_lift.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
        
        return new $HC_4_0$TParsec__Success__MkSuccess($_1_lift.$1, $_6_in, Prelude__Nat__lteRefl($_6_in.add((new $JSRTS.jsbn.BigInteger(("1"))))), $_1_lift.$2);
    }
}

// Typedefs.{getUsedIndices_68}

function Typedefs___123_getUsedIndices_95_68_125_($_0_lift, $_1_lift, $_2_lift){
    return Prelude__Interfaces__Data__Fin___64_Prelude__Interfaces__Eq_36_Fin_32_n_58__33__61__61__58_0($_0_lift, $_1_lift, $_2_lift);
}

// Typedefs.{getUsedIndices_69}

function Typedefs___123_getUsedIndices_95_69_125_($_0_lift, $_1_lift, $_2_lift){
    return Prelude__List___43__43_(null, Typedefs__getUsedIndices($_0_lift, $_1_lift), $_2_lift);
}

// Typedefs.{getUsedIndices_70}

function Typedefs___123_getUsedIndices_95_70_125_($_0_lift, $_1_lift){
    return Data__Vect__index(null, null, $_1_lift, $_0_lift);
}

// Typedefs.{getUsedIndices_72}

function Typedefs___123_getUsedIndices_95_72_125_($_0_lift, $_1_lift){
    let $cg$1 = null;
    if(($_0_lift.type === 1)) {
        $cg$1 = new $HC_2_1$Prelude__List___58__58_($_0_lift.$1, $HC_0_0$Prelude__List__Nil);
    } else {
        $cg$1 = $HC_0_0$Prelude__List__Nil;
    }
    
    return Prelude__List___43__43_(null, $cg$1, $_1_lift);
}

// Typedefs.{getUsedIndices_73}

function Typedefs___123_getUsedIndices_95_73_125_($_0_lift, $_1_lift, $_2_lift){
    let $cg$1 = null;
    $cg$1 = $_1_lift.$2;
    return Prelude__List___43__43_(null, Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $partial_0_2$Typedefs___123_getUsedIndices_95_72_125_(), $HC_0_0$Prelude__List__Nil, Typedefs__getUsedIndices($_0_lift.add((new $JSRTS.jsbn.BigInteger(("1")))), $cg$1)), $_2_lift);
}

// TParsec.Combinators.{guardM_82}

function TParsec__Combinators___123_guardM_95_82_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    
    let $cg$2 = null;
    const $cg$4 = $_1_lift.$1;
    $cg$2 = $cg$4.$2(null)($_2_lift);
    return $_0_lift.$3(null)($cg$2)($_3_lift);
}

// TParsec.Combinators.{guardM_83}

function TParsec__Combinators___123_guardM_95_83_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return new $HC_4_0$TParsec__Success__MkSuccess($_3_lift, $_0_lift, $_1_lift, $_2_lift);
}

// TParsec.Combinators.{guardM_84}

function TParsec__Combinators___123_guardM_95_84_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    let $cg$1 = null;
    $cg$1 = $_0_lift.$2(null);
    let $cg$2 = null;
    $cg$2 = Prelude__Functor__Prelude___64_Prelude__Functor__Functor_36_Maybe_58__33_map_58_0(null, null, $partial_3_4$TParsec__Combinators___123_guardM_95_83_125_($_3_lift.$2, $_3_lift.$3, $_3_lift.$4), $_2_lift($_3_lift.$1));
    return Prelude__Foldable__Prelude__Maybe___64_Prelude__Foldable__Foldable_36_Maybe_58__33_foldr_58_0(null, null, $partial_2_4$TParsec__Combinators___123_guardM_95_82_125_($_0_lift, $_1_lift), $cg$1, $cg$2);
}

// Backend.Haskell.{hsParam_86}

function Backend__Haskell___123_hsParam_95_86_125_($_0_lift){
    return new $HC_1_3$Backend__Haskell__HsVar($_0_lift);
}

// Typedefs.{idVars_87}

function Typedefs___123_idVars_95_87_125_($_0_lift){
    return new $HC_1_4$Typedefs__TVar($_0_lift);
}

// Backend.Utils.{ifNotPresent_88}

function Backend__Utils___123_ifNotPresent_95_88_125_($_0_lift, $_1_lift, $_2_lift){
    return $_2_lift;
}

// Backend.Utils.{ifNotPresent_91}

function Backend__Utils___123_ifNotPresent_95_91_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return $_3_lift($_2_lift);
}

// Backend.Utils.{ifNotPresent_92}

function Backend__Utils___123_ifNotPresent_95_92_125_($_0_lift){
    return new $HC_2_0$Builtins__MkPair($_0_lift, $_0_lift);
}

// Backend.Utils.{ifNotPresent_104}

function Backend__Utils___123_ifNotPresent_95_104_125_($_0_lift, $_1_lift, $_2_lift){
    return new $HC_2_0$Builtins__MkPair($HC_0_0$MkUnit, new $HC_2_1$Prelude__List___58__58_($_0_lift, $_1_lift));
}

// Backend.Utils.{ifNotPresent_105}

function Backend__Utils___123_ifNotPresent_95_105_125_($_0_lift){
    return new $HC_2_0$Builtins__MkPair($HC_0_0$Prelude__List__Nil, $_0_lift);
}

// Backend.Utils.{ifNotPresent_106}

function Backend__Utils___123_ifNotPresent_95_106_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    let $cg$1 = null;
    $cg$1 = $_0_lift.$1;
    
    if(Prelude__List__elemBy(null, $cg$1, $_1_lift, $_3_lift)) {
        return $partial_0_1$Backend__Utils___123_ifNotPresent_95_105_125_();
    } else {
        return $partial_7_8$Prelude__Applicative__Control__Monad__State___64_Prelude__Applicative__Applicative_36_StateT_32_stateType_32_f_58__33__60__42__62__58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), $partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_()), $partial_0_4$Backend__Utils___123_ifNotPresent_95_91_125_()), $partial_7_8$Prelude__Functor__Control__Monad__State___64_Prelude__Functor__Functor_36_StateT_32_stateType_32_f_58__33_map_58_0(null, null, null, null, $partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), $partial_7_8$Prelude__Monad__Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), $partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_()), $partial_0_4$Backend__Utils___123_ifNotPresent_95_91_125_()), $partial_0_1$Backend__Utils___123_ifNotPresent_95_92_125_(), $partial_1_3$Backend__Utils___123_ifNotPresent_95_104_125_($_1_lift))), $_2_lift);
    }
}

// Parse.{ignorespaces_107}

function Parse___123_ignorespaces_95_107_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift, $_7_lift, $_8_lift, $_9_lift, $_10_lift){
    return Parse__comments(null, $_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift)($_9_lift)(Prelude__Nat__lteTransitive(null, null, null, $_10_lift, null));
}

// TParsec.Combinators.{land_108}

function TParsec__Combinators___123_land_95_108_125_($_0_lift){
    
    return $_0_lift.$1;
}

// Backend.Haskell.{makeDefs_123}

function Backend__Haskell___123_makeDefs_95_123_125_($_0_lift, $_1_lift){
    return Prelude__List___43__43_(null, $_0_lift, $_1_lift);
}

// Backend.Haskell.{makeDefs_125}

function Backend__Haskell___123_makeDefs_95_125_125_($_0_lift){
    return Data__Vect__foldrImpl(null, null, null, $partial_0_2$Backend__Haskell___123_makeDefs_95_123_125_(), $HC_0_0$Prelude__List__Nil, $partial_0_1$Typedefs___123_apN_95_20_125_(), $_0_lift);
}

// Backend.Haskell.{makeDefs_127}

function Backend__Haskell___123_makeDefs_95_127_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return $partial_7_8$Prelude__Functor__Control__Monad__State___64_Prelude__Functor__Functor_36_StateT_32_stateType_32_f_58__33_map_58_0(null, null, null, null, $partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_(), $_2_lift, $_3_lift);
}

// Backend.Haskell.{makeDefs_128}

function Backend__Haskell___123_makeDefs_95_128_125_($_0_lift, $_1_lift, $_2_lift){
    return new $HC_2_0$Builtins__MkPair($_1_lift, $_2_lift);
}

// Backend.Haskell.{makeDefs_133}

function Backend__Haskell___123_makeDefs_95_133_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return $partial_7_8$Prelude__Applicative__Control__Monad__State___64_Prelude__Applicative__Applicative_36_StateT_32_stateType_32_f_58__33__60__42__62__58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), $partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_()), $partial_0_4$Backend__Utils___123_ifNotPresent_95_91_125_()), $_2_lift, $_3_lift);
}

// Backend.Haskell.{makeDefs_134}

function Backend__Haskell___123_makeDefs_95_134_125_($_0_lift, $_1_lift, $_2_lift){
    return new $HC_2_0$Builtins__MkPair(Prelude__List___43__43_(null, $_0_lift, $_1_lift), $_2_lift);
}

// Backend.Haskell.{makeDefs_135}

function Backend__Haskell___123_makeDefs_95_135_125_($_0_lift, $_1_lift, $_2_lift){
    return $partial_7_8$Prelude__Monad__Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), $partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_()), $partial_0_4$Backend__Utils___123_ifNotPresent_95_91_125_()), $partial_7_8$Prelude__Functor__Control__Monad__State___64_Prelude__Functor__Functor_36_StateT_32_stateType_32_f_58__33_map_58_0(null, null, null, null, $partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_(), $partial_0_1$Backend__Haskell___123_makeDefs_95_125_125_(), Prelude__Traversable__Data__Vect___64_Prelude__Traversable__Traversable_36_Vect_32_n_58__33_traverse_58_0(null, null, null, null, new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_127_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_128_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_133_125_()), $partial_1_2$Backend__Haskell__makeDefs($_0_lift), $_1_lift)), $partial_1_3$Backend__Haskell___123_makeDefs_95_134_125_($_2_lift));
}

// Backend.JSON.{makeDefs_161}

function Backend__JSON___123_makeDefs_95_161_125_($_0_lift, $_1_lift){
    return ($_0_lift == $_1_lift);
}

// Backend.JSON.{makeDefs_162}

function Backend__JSON___123_makeDefs_95_162_125_($_0_lift, $_1_lift){
    
    if((((($_0_lift == $_1_lift)) ? 1|0 : 0|0) === 0)) {
        return true;
    } else {
        return false;
    }
}

// Backend.JSON.{makeDefs_163}

function Backend__JSON___123_makeDefs_95_163_125_($_0_lift){
    return new $HC_2_0$Builtins__MkPair(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("emptyType", Backend__JSON__makeDefs_58_emptyType_58_0()), $HC_0_0$Prelude__List__Nil), $_0_lift);
}

// Backend.JSON.{makeDefs_166}

function Backend__JSON___123_makeDefs_95_166_125_($_0_lift){
    return new $HC_2_0$Builtins__MkPair(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("singletonType", Backend__JSON__makeDefs_58_singletonType_58_1()), $HC_0_0$Prelude__List__Nil), $_0_lift);
}

// Backend.ReasonML.{makeDefs_213}

function Backend__ReasonML___123_makeDefs_95_213_125_($_0_lift, $_1_lift, $_2_lift){
    return $partial_7_8$Prelude__Monad__Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), $partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_()), $partial_0_4$Backend__Utils___123_ifNotPresent_95_91_125_()), $partial_7_8$Prelude__Functor__Control__Monad__State___64_Prelude__Functor__Functor_36_StateT_32_stateType_32_f_58__33_map_58_0(null, null, null, null, $partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_(), $partial_0_1$Backend__Haskell___123_makeDefs_95_125_125_(), Prelude__Traversable__Data__Vect___64_Prelude__Traversable__Traversable_36_Vect_32_n_58__33_traverse_58_0(null, null, null, null, new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_127_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_128_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_133_125_()), $partial_1_2$Backend__ReasonML__makeDefs($_0_lift), $_1_lift)), $partial_1_3$Backend__Haskell___123_makeDefs_95_134_125_($_2_lift));
}

// Backend.ReasonML.{makeDefs_243}

function Backend__ReasonML___123_makeDefs_95_243_125_($_0_lift, $_1_lift){
    return Prelude__List___43__43_(null, $_1_lift, $_0_lift);
}

// Backend.ReasonML.{makeDefs_244}

function Backend__ReasonML___123_makeDefs_95_244_125_($_0_lift){
    return $partial_7_8$Prelude__Functor__Control__Monad__State___64_Prelude__Functor__Functor_36_StateT_32_stateType_32_f_58__33_map_58_0(null, null, null, null, $partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_(), $partial_1_2$Backend__ReasonML___123_makeDefs_95_243_125_($_0_lift), Backend__ReasonML__makeDefs_39_((new $JSRTS.jsbn.BigInteger(("2"))), Backend__ReasonML__makeDefs_58_eitherDef_58_3(null, null, null)));
}

// Backend.Haskell.{makeDefs'_248}

function Backend__Haskell___123_makeDefs_39__95_248_125_($_0_lift){
    return (!(!($_0_lift.type === 0)));
}

// Backend.Haskell.{makeDefs'_249}

function Backend__Haskell___123_makeDefs_39__95_249_125_($_0_lift){
    
    if(($_0_lift.type === 0)) {
        return $_0_lift.$1;
    } else {
        return "";
    }
}

// Backend.Haskell.{makeDefs'_250}

function Backend__Haskell___123_makeDefs_39__95_250_125_($_0_lift){
    return (!(!($_0_lift.type === 0)));
}

// Backend.Haskell.{makeDefs'_251}

function Backend__Haskell___123_makeDefs_39__95_251_125_($_0_lift, $_1_lift, $_2_lift){
    
    return new $HC_2_0$Builtins__MkPair($_2_lift.$1, Backend__Haskell__makeType($_0_lift.add((new $JSRTS.jsbn.BigInteger(("1")))), $_1_lift, $_2_lift.$2));
}

// Backend.Haskell.{makeDefs'_258}

function Backend__Haskell___123_makeDefs_39__95_258_125_($_0_lift){
    return Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $partial_0_2$Backend__Haskell___123_makeDefs_95_123_125_(), $HC_0_0$Prelude__List__Nil, $_0_lift);
}

// Backend.Haskell.{makeDefs'_267}

function Backend__Haskell___123_makeDefs_39__95_267_125_($_0_lift, $_1_lift){
    
    return Backend__Haskell__makeDefs($_0_lift.add((new $JSRTS.jsbn.BigInteger(("1")))), $_1_lift.$2);
}

// Backend.Haskell.{makeDefs'_270}

function Backend__Haskell___123_makeDefs_39__95_270_125_($_0_lift){
    return (!(!($_0_lift.type === 0)));
}

// Backend.Haskell.{makeDefs'_271}

function Backend__Haskell___123_makeDefs_39__95_271_125_($_0_lift){
    
    if(($_0_lift.type === 0)) {
        return $_0_lift.$1;
    } else {
        return "";
    }
}

// Backend.Haskell.{makeDefs'_272}

function Backend__Haskell___123_makeDefs_39__95_272_125_($_0_lift){
    return (!(!($_0_lift.type === 0)));
}

// Backend.Haskell.{makeDefs'_273}

function Backend__Haskell___123_makeDefs_39__95_273_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift){
    const $cg$2 = Data__Vect__filter(null, null, $partial_0_1$Backend__Haskell___123_makeDefs_39__95_270_125_(), Typedefs__getUsedVars(null, $_0_lift, Backend__Utils__freshEnv($_0_lift, "x"), $_1_lift));
    let $cg$1 = null;
    $cg$1 = $cg$2.$1;
    const $cg$4 = Data__Vect__filter(null, null, $partial_0_1$Backend__Haskell___123_makeDefs_39__95_272_125_(), Typedefs__getUsedVars(null, $_0_lift, Backend__Utils__freshEnv($_0_lift, "x"), $_1_lift));
    let $cg$3 = null;
    $cg$3 = Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Backend__Haskell___123_makeDefs_39__95_271_125_(), $cg$4.$2);
    return new $HC_2_0$Builtins__MkPair(new $HC_2_1$Prelude__List___58__58_(new $HC_2_1$Backend__Haskell__ADT(new $HC_3_0$Backend__Utils__MkDecl($cg$1, $_2_lift, $cg$3), $_3_lift), $_4_lift), $_5_lift);
}

// Backend.Haskell.{makeDefs'_278}

function Backend__Haskell___123_makeDefs_39__95_278_125_($_0_lift){
    return (!(!($_0_lift.type === 0)));
}

// Backend.Haskell.{makeDefs'_279}

function Backend__Haskell___123_makeDefs_39__95_279_125_($_0_lift){
    
    if(($_0_lift.type === 0)) {
        return $_0_lift.$1;
    } else {
        return "";
    }
}

// Backend.Haskell.{makeDefs'_280}

function Backend__Haskell___123_makeDefs_39__95_280_125_($_0_lift){
    return (!(!($_0_lift.type === 0)));
}

// Backend.Haskell.{makeDefs'_281}

function Backend__Haskell___123_makeDefs_39__95_281_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    const $cg$2 = Data__Vect__filter(null, null, $partial_0_1$Backend__Haskell___123_makeDefs_39__95_278_125_(), Typedefs__getUsedVars(null, $_0_lift, Backend__Utils__freshEnv($_0_lift, "x"), $_1_lift));
    let $cg$1 = null;
    $cg$1 = $cg$2.$1;
    const $cg$4 = Data__Vect__filter(null, null, $partial_0_1$Backend__Haskell___123_makeDefs_39__95_280_125_(), Typedefs__getUsedVars(null, $_0_lift, Backend__Utils__freshEnv($_0_lift, "x"), $_1_lift));
    let $cg$3 = null;
    $cg$3 = Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Backend__Haskell___123_makeDefs_39__95_279_125_(), $cg$4.$2);
    return new $HC_2_0$Builtins__MkPair(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Backend__Haskell__Synonym(new $HC_3_0$Backend__Utils__MkDecl($cg$1, $_2_lift, $cg$3), Backend__Haskell__makeType($_0_lift, Backend__Utils__freshEnv($_0_lift, "x"), $_1_lift)), $_3_lift), $_4_lift);
}

// Backend.JSON.{makeDefs'_284}

function Backend__JSON___123_makeDefs_39__95_284_125_($_0_lift, $_1_lift){
    
    return new $HC_2_0$Builtins__MkPair($_1_lift.$1, Backend__Utils__flattenMus_58_flattenMu_58_0((new $JSRTS.jsbn.BigInteger(("0"))), null, new $HC_2_1$Data__Vect___58__58_($_0_lift, $HC_0_0$Data__Vect__Nil), $_1_lift.$2));
}

// Backend.JSON.{makeDefs'_301}

function Backend__JSON___123_makeDefs_39__95_301_125_($_0_lift){
    let $cg$1 = null;
    $cg$1 = $_0_lift.$2;
    return Backend__JSON__makeDefs($cg$1);
}

// Backend.JSON.{makeDefs'_302}

function Backend__JSON___123_makeDefs_39__95_302_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return new $HC_2_0$Builtins__MkPair(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair($_0_lift, Backend__JSON__disjointSubSchema(null, $_1_lift)), $_2_lift), $_3_lift);
}

// Backend.JSON.{makeDefs'_307}

function Backend__JSON___123_makeDefs_39__95_307_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return new $HC_2_0$Builtins__MkPair(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair($_0_lift, Backend__JSON__makeSubSchema($_1_lift)), $_2_lift), $_3_lift);
}

// Backend.ReasonML.{makeDefs'_313}

function Backend__ReasonML___123_makeDefs_39__95_313_125_($_0_lift, $_1_lift, $_2_lift){
    
    return new $HC_2_0$Builtins__MkPair($_2_lift.$1, Backend__ReasonML__makeType($_0_lift.add((new $JSRTS.jsbn.BigInteger(("1")))), $_1_lift, $_2_lift.$2));
}

// Backend.ReasonML.{makeDefs'_329}

function Backend__ReasonML___123_makeDefs_39__95_329_125_($_0_lift, $_1_lift){
    
    return Backend__ReasonML__makeDefs($_0_lift.add((new $JSRTS.jsbn.BigInteger(("1")))), $_1_lift.$2);
}

// Backend.ReasonML.{makeDefs'_335}

function Backend__ReasonML___123_makeDefs_39__95_335_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift){
    const $cg$2 = Data__Vect__filter(null, null, $partial_0_1$Backend__Haskell___123_makeDefs_39__95_270_125_(), Typedefs__getUsedVars(null, $_1_lift, Backend__Utils__freshEnv($_1_lift, "\'x"), $_2_lift));
    let $cg$1 = null;
    $cg$1 = $cg$2.$1;
    const $cg$4 = Data__Vect__filter(null, null, $partial_0_1$Backend__Haskell___123_makeDefs_39__95_272_125_(), Typedefs__getUsedVars(null, $_1_lift, Backend__Utils__freshEnv($_1_lift, "\'x"), $_2_lift));
    let $cg$3 = null;
    $cg$3 = Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Backend__Haskell___123_makeDefs_39__95_271_125_(), $cg$4.$2);
    return new $HC_2_0$Builtins__MkPair(new $HC_2_1$Prelude__List___58__58_(new $HC_3_1$Backend__ReasonML__Variant($_0_lift, new $HC_3_0$Backend__Utils__MkDecl($cg$1, $_3_lift, $cg$3), $_4_lift), $_5_lift), $_6_lift);
}

// Backend.ReasonML.{makeDefs'_343}

function Backend__ReasonML___123_makeDefs_39__95_343_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    const $cg$2 = Data__Vect__filter(null, null, $partial_0_1$Backend__Haskell___123_makeDefs_39__95_278_125_(), Typedefs__getUsedVars(null, $_0_lift, Backend__Utils__freshEnv($_0_lift, "\'x"), $_1_lift));
    let $cg$1 = null;
    $cg$1 = $cg$2.$1;
    const $cg$4 = Data__Vect__filter(null, null, $partial_0_1$Backend__Haskell___123_makeDefs_39__95_280_125_(), Typedefs__getUsedVars(null, $_0_lift, Backend__Utils__freshEnv($_0_lift, "\'x"), $_1_lift));
    let $cg$3 = null;
    $cg$3 = Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Backend__Haskell___123_makeDefs_39__95_279_125_(), $cg$4.$2);
    return new $HC_2_0$Builtins__MkPair(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Backend__ReasonML__Alias(new $HC_3_0$Backend__Utils__MkDecl($cg$1, $_2_lift, $cg$3), Backend__ReasonML__makeType($_0_lift, Backend__Utils__freshEnv($_0_lift, "\'x"), $_1_lift)), $_3_lift), $_4_lift);
}

// Typedefs.{makeName_348}

function Typedefs___123_makeName_95_348_125_($_0_lift, $_1_lift){
    let $cg$1 = null;
    $cg$1 = $_0_lift.$1;
    return ($cg$1 + $_1_lift);
}

// Backend.JSON.{makeSubSchema_358}

function Backend__JSON___123_makeSubSchema_95_358_125_($_0_lift, $_1_lift){
    return new $HC_2_0$Builtins__MkPair($_0_lift, $_1_lift);
}

// Backend.Haskell.{makeType_360}

function Backend__Haskell___123_makeType_95_360_125_($_0_lift){
    
    if(($_0_lift.type === 0)) {
        return new $HC_1_3$Backend__Haskell__HsVar($_0_lift.$1);
    } else {
        const $cg$3 = $_0_lift.$1;
        return new $HC_3_4$Backend__Haskell__HsParam($cg$3.$1, $cg$3.$2, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Backend__Haskell___123_hsParam_95_86_125_(), $cg$3.$3));
    }
}

// Backend.Haskell.{makeType_361}

function Backend__Haskell___123_makeType_95_361_125_($_0_lift, $_1_lift){
    return new $HC_3_4$Backend__Haskell__HsParam((new $JSRTS.jsbn.BigInteger(("2"))), "Either", new $HC_2_1$Data__Vect___58__58_($_0_lift, new $HC_2_1$Data__Vect___58__58_($_1_lift, $HC_0_0$Data__Vect__Nil)));
}

// Backend.ReasonML.{makeType_363}

function Backend__ReasonML___123_makeType_95_363_125_($_0_lift){
    return new $HC_1_2$Backend__ReasonML__RMLVar($_0_lift);
}

// Backend.ReasonML.{makeType_364}

function Backend__ReasonML___123_makeType_95_364_125_($_0_lift){
    
    if(($_0_lift.type === 0)) {
        return new $HC_1_2$Backend__ReasonML__RMLVar($_0_lift.$1);
    } else {
        const $cg$3 = $_0_lift.$1;
        return new $HC_3_3$Backend__ReasonML__RMLParam($cg$3.$1, $cg$3.$2, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Backend__ReasonML___123_makeType_95_363_125_(), $cg$3.$3));
    }
}

// Backend.ReasonML.{makeType_365}

function Backend__ReasonML___123_makeType_95_365_125_($_0_lift, $_1_lift){
    return new $HC_3_3$Backend__ReasonML__RMLParam((new $JSRTS.jsbn.BigInteger(("2"))), "Either", new $HC_2_1$Data__Vect___58__58_($_0_lift, new $HC_2_1$Data__Vect___58__58_($_1_lift, $HC_0_0$Data__Vect__Nil)));
}

// TParsec.Combinators.{mand_367}

function TParsec__Combinators___123_mand_95_367_125_($_0_lift, $_1_lift){
    
    return new $HC_4_0$TParsec__Success__MkSuccess(new $HC_2_0$Builtins__MkPair($_0_lift, $_1_lift.$1), $_1_lift.$2, $_1_lift.$3, $_1_lift.$4);
}

// TParsec.Combinators.{mand_368}

function TParsec__Combinators___123_mand_95_368_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift){
    
    const $cg$3 = $_0_lift.$1;
    return $cg$3.$1(null)(null)($partial_1_2$TParsec__Combinators___123_mand_95_367_125_($_5_lift))($_1_lift($_2_lift)($_3_lift)($_4_lift));
}

// TParsec.Combinators.{map_369}

function TParsec__Combinators___123_map_95_369_125_($_0_lift, $_1_lift){
    
    return new $HC_4_0$TParsec__Success__MkSuccess($_0_lift($_1_lift.$1), $_1_lift.$2, $_1_lift.$3, $_1_lift.$4);
}

// Backend.Utils.{nameMu_370}

function Backend__Utils___123_nameMu_95_370_125_($_0_lift, $_1_lift){
    let $cg$1 = null;
    $cg$1 = $_0_lift.$1;
    let $cg$2 = null;
    if((((($cg$1 == "")) ? 1|0 : 0|0) === 0)) {
        $cg$2 = true;
    } else {
        $cg$2 = false;
    }
    
    const $cg$4 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$2, true);
    let $cg$3 = null;
    if(($cg$4.type === 1)) {
        $cg$3 = "";
    } else {
        let $cg$5 = null;
        $cg$5 = $_0_lift.$1;
        let $cg$6 = null;
        if(Prelude__Chars__isLower($cg$5[0])) {
            let $cg$8 = null;
            $cg$8 = $_0_lift.$1;
            $cg$6 = String.fromCharCode(((($cg$8[0]).charCodeAt(0)|0) - 32));
        } else {
            let $cg$7 = null;
            $cg$7 = $_0_lift.$1;
            $cg$6 = $cg$7[0];
        }
        
        let $cg$9 = null;
        $cg$9 = $_0_lift.$1;
        $cg$3 = (($cg$6)+($cg$9.slice(1)));
    }
    
    return ($cg$3 + $_1_lift);
}

// Backend.JSON.{nary_372}

function Backend__JSON___123_nary_95_372_125_($_0_lift, $_1_lift){
    return ($_0_lift + Prelude__Show__primNumShow(null, $partial_0_1$prim_95__95_toStrBigInt(), $HC_0_0$Prelude__Show__Open, Data__Fin__finToNat(null, $_1_lift)));
}

// Parse.{neComments_374}

function Parse___123_neComments_95_374_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift, $_7_lift, $_8_lift, $_9_lift, $_10_lift){
    let $cg$1 = null;
    const $cg$3 = $_0_lift.$1;
    $cg$1 = $cg$3.$1;
    return $partial_10_11$TParsec__Combinators__map(null, null, null, null, $cg$1, $partial_0_1$Parse___123_emptyComments_95_33_125_(), null, TParsec__Combinators__nelist(null, null, null, $_1_lift, $_0_lift, $_2_lift)(ParserUtils__notChar(null, $_3_lift, $_1_lift, $_0_lift, $_4_lift, $_5_lift, $_6_lift, "\n")($_2_lift)), $_9_lift, Prelude__Nat__lteTransitive(null, null, null, $_10_lift, null));
}

// Parse.{neComments_375}

function Parse___123_neComments_95_375_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift, $_7_lift, $_8_lift, $_9_lift, $_10_lift){
    return TParsec__Combinators__Chars__char(null, $_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, "\n")($_6_lift)($_9_lift)(Prelude__Nat__lteTransitive(null, null, null, $_10_lift, null));
}

// TParsec.Combinators.{nelist_376}

function TParsec__Combinators___123_nelist_95_376_125_($_0_lift){
    
    return Data__NEList__consopt(null, $_0_lift.$1, $_0_lift.$2);
}

// TParsec.Combinators.{nelist_377}

function TParsec__Combinators___123_nelist_95_377_125_($_0_lift, $_1_lift, $_2_lift){
    return $_0_lift($_1_lift)(Prelude__Nat__lteTransitive(null, null, null, $_2_lift, null));
}

// TParsec.Combinators.{nelist_378}

function TParsec__Combinators___123_nelist_95_378_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    return $_0_lift($_3_lift)($_4_lift)($partial_1_3$TParsec__Combinators___123_nelist_95_377_125_($_1_lift));
}

// TParsec.Combinators.{nelist_379}

function TParsec__Combinators___123_nelist_95_379_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    let $cg$1 = null;
    const $cg$3 = $_0_lift.$1;
    $cg$1 = $cg$3.$1;
    return $partial_8_11$TParsec__Combinators__map(null, null, null, null, $cg$1, $partial_0_1$TParsec__Combinators___123_nelist_95_376_125_(), null, $partial_9_12$TParsec__Combinators__andoptbind(null, null, null, null, $_0_lift, $_1_lift, null, $_4_lift, $partial_2_5$TParsec__Combinators___123_nelist_95_378_125_($_3_lift, $_4_lift)));
}

// TParsec.Combinators.{optand_380}

function TParsec__Combinators___123_optand_95_380_125_($_0_lift){
    return new $HC_1_1$Prelude__Maybe__Just($_0_lift);
}

// TParsec.Combinators.{optand_382}

function TParsec__Combinators___123_optand_95_382_125_($_0_lift){
    return new $HC_2_0$Builtins__MkPair($HC_0_0$Prelude__Maybe__Nothing, $_0_lift);
}

// TParsec.Combinators.Chars.{parens_383}

function TParsec__Combinators__Chars___123_parens_95_383_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift, $_7_lift, $_8_lift, $_9_lift, $_10_lift){
    return TParsec__Combinators__Chars__char(null, $_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, ")")($_6_lift)($_9_lift)(Prelude__Nat__lteTransitive(null, null, null, $_10_lift, null));
}

// TParsec.Running.{parseMaybe_384}

function TParsec__Running___123_parseMaybe_95_384_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return Prelude__Functor__Prelude___64_Prelude__Functor__Functor_36_Maybe_58__33_map_58_0(null, null, $_2_lift, $_3_lift);
}

// TParsec.Running.{parseMaybe_385}

function TParsec__Running___123_parseMaybe_95_385_125_($_0_lift, $_1_lift){
    return new $HC_1_1$Prelude__Maybe__Just($_1_lift);
}

// TParsec.Running.{parseMaybe_386}

function TParsec__Running___123_parseMaybe_95_386_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return Prelude__Applicative__Prelude___64_Prelude__Applicative__Applicative_36_Maybe_58__33__60__42__62__58_0(null, null, $_2_lift, $_3_lift);
}

// TParsec.Running.{parseMaybe_387}

function TParsec__Running___123_parseMaybe_95_387_125_($_0_lift){
    
    return $_0_lift.$1;
}

// TParsec.Running.{parseMaybe_388}

function TParsec__Running___123_parseMaybe_95_388_125_($_0_lift){
    let $cg$1 = null;
    $cg$1 = $_0_lift.$2;
    return Prelude__Maybe__toMaybe(null, Prelude__Interfaces__Prelude__Nat___64_Prelude__Interfaces__Eq_36_Nat_58__33__61__61__58_0($cg$1, (new $JSRTS.jsbn.BigInteger(("0")))), new $JSRTS.Lazy((function(){
        return (function(){
            return TParsec__Running___123_parseMaybe_95_387_125_($_0_lift);
        })();
    })));
}

// Parse.{parseTNamed_389}

function Parse___123_parseTNamed_95_389_125_($_0_lift, $_1_lift){
    return TParsec__Running__Parse___64_TParsec__Running__MonadRun_36_StateT_32_PState_32_Identity_58__33_runMonad_58_0(null, $_1_lift);
}

// Parse.{parseTNamed_390}

function Parse___123_parseTNamed_95_390_125_($_0_lift, $_1_lift){
    return TParsec__Running__TParsec__Running___64_TParsec__Running__MonadRun_36_TParsecT_32_e_32_a_32_m_58__33_runMonad_58_0(null, null, null, null, $partial_0_2$Parse___123_parseTNamed_95_389_125_(), $_1_lift);
}

// Parse.{parseTNamed_391}

function Parse___123_parseTNamed_95_391_125_($_0_lift){
    let $cg$1 = null;
    if((((($_0_lift == "")) ? 1|0 : 0|0) === 0)) {
        $cg$1 = true;
    } else {
        $cg$1 = false;
    }
    
    const $cg$3 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$1, true);
    if(($cg$3.type === 1)) {
        return $HC_0_0$Prelude__List__Nil;
    } else {
        let $cg$4 = null;
        if((((($_0_lift.slice(1) == "")) ? 1|0 : 0|0) === 0)) {
            $cg$4 = true;
        } else {
            $cg$4 = false;
        }
        
        const $cg$6 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$4, true);
        let $cg$5 = null;
        if(($cg$6.type === 1)) {
            $cg$5 = $HC_0_0$Prelude__Strings__StrNil;
        } else {
            $cg$5 = new $HC_2_1$Prelude__Strings__StrCons($_0_lift.slice(1)[0], $_0_lift.slice(1).slice(1));
        }
        
        return new $HC_2_1$Prelude__List___58__58_($_0_lift[0], _95_Prelude__Strings__unpack_95_with_95_36(null, $cg$5));
    }
}

// Parse.{parseTNamed_392}

function Parse___123_parseTNamed_95_392_125_($_0_lift){
    return Data__Inspect__MkSizedList(null, $_0_lift);
}

// Backend.JSON.{productSubSchema_395}

function Backend__JSON___123_productSubSchema_95_395_125_($_0_lift){
    return new $HC_1_3$Language__JSON__Data__JString($_0_lift);
}

// TParsec.Combinators.{rand_399}

function TParsec__Combinators___123_rand_95_399_125_($_0_lift){
    
    return $_0_lift.$2;
}

// TParsec.Combinators.{randbindm_401}

function TParsec__Combinators___123_randbindm_95_401_125_($_0_lift){
    
    return $_0_lift.$2;
}

// Data.Vect.{range_402}

function Data__Vect___123_range_95_402_125_($_0_lift){
    return new $HC_1_1$Data__Fin__FS($_0_lift);
}

// Backend.Haskell.{renderApp_403}

function Backend__Haskell___123_renderApp_95_403_125_($_0_lift, $_1_lift){
    return new $HC_2_4$Text__PrettyPrint__WL__Core__Cat($_0_lift, new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__char(" "), $_1_lift));
}

// Backend.Haskell.{renderDef_410}

function Backend__Haskell___123_renderDef_95_410_125_($_0_lift){
    let $cg$1 = null;
    if((((($_0_lift == "")) ? 1|0 : 0|0) === 0)) {
        $cg$1 = true;
    } else {
        $cg$1 = false;
    }
    
    const $cg$3 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$1, true);
    let $cg$2 = null;
    if(($cg$3.type === 1)) {
        $cg$2 = "";
    } else {
        let $cg$4 = null;
        if(Prelude__Chars__isUpper($_0_lift[0])) {
            $cg$4 = String.fromCharCode(((($_0_lift[0]).charCodeAt(0)|0) + 32));
        } else {
            $cg$4 = $_0_lift[0];
        }
        
        $cg$2 = (($cg$4)+($_0_lift.slice(1)));
    }
    
    return Text__PrettyPrint__WL__Core__text($cg$2);
}

// Backend.Haskell.{renderDef_414}

function Backend__Haskell___123_renderDef_95_414_125_($_0_lift){
    let $cg$1 = null;
    if((((($_0_lift == "")) ? 1|0 : 0|0) === 0)) {
        $cg$1 = true;
    } else {
        $cg$1 = false;
    }
    
    const $cg$3 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$1, true);
    let $cg$2 = null;
    if(($cg$3.type === 1)) {
        $cg$2 = "";
    } else {
        let $cg$4 = null;
        if(Prelude__Chars__isUpper($_0_lift[0])) {
            $cg$4 = String.fromCharCode(((($_0_lift[0]).charCodeAt(0)|0) + 32));
        } else {
            $cg$4 = $_0_lift[0];
        }
        
        $cg$2 = (($cg$4)+($_0_lift.slice(1)));
    }
    
    return Text__PrettyPrint__WL__Core__text($cg$2);
}

// Typedefs.{shiftVars_427}

function Typedefs___123_shiftVars_95_427_125_($_0_lift){
    
    return new $HC_2_0$Builtins__MkPair($_0_lift.$1, Typedefs__shiftVars(null, $_0_lift.$2));
}

// Language.JSON.Data.{showString_428}

function Language__JSON__Data___123_showString_95_428_125_($_0_lift, $_1_lift){
    return (Language__JSON__Data__showChar($_0_lift) + $_1_lift);
}

// TParsec.Combinators.Chars.{string_430}

function TParsec__Combinators__Chars___123_string_95_430_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift, $_7_lift){
    return TParsec__Combinators__Chars__char(null, $_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_7_lift)($_6_lift);
}

// Parse.{tdef_431}

function Parse___123_tdef_95_431_125_($_0_lift, $_1_lift, $_2_lift){
    return new $HC_2_0$Builtins__MkPair(new $HC_1_2$TParsec__Result__Value(new $HC_2_0$Builtins__MkPair($HC_0_0$MkUnit, $_1_lift)), $_2_lift);
}

// Parse.{tdef_434}

function Parse___123_tdef_95_434_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return Prelude__Functor__TParsec__Types___64_Prelude__Functor__Functor_36_TParsecT_32_e_32_a_32_m_58__33_map_58_0(null, null, null, null, null, $partial_0_4$Backend__Haskell___123_makeDefs_95_127_125_(), $_2_lift, $_3_lift);
}

// Parse.{tdef_447}

function Parse___123_tdef_95_447_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return $partial_7_8$Prelude__Monad__Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), $partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_()), $partial_0_4$Backend__Utils___123_ifNotPresent_95_91_125_()), $_2_lift, $_3_lift);
}

// Parse.{tdef_448}

function Parse___123_tdef_95_448_125_($_0_lift, $_1_lift){
    return $partial_6_7$Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33_pure_58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_127_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_128_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_133_125_()), $partial_0_4$Parse___123_tdef_95_447_125_()), $_1_lift);
}

// Parse.{tdef_462}

function Parse___123_tdef_95_462_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0(null, null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_127_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_128_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_133_125_()), $partial_0_4$Parse___123_tdef_95_447_125_()), $_2_lift, $_3_lift);
}

// Parse.{tdef_477}

function Parse___123_tdef_95_477_125_($_0_lift){
    return $partial_6_7$Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Alternative_36_TParsecT_32_e_32_a_32_m_58__33_empty_58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_127_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_128_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_133_125_()), $partial_0_4$Parse___123_tdef_95_447_125_()), $partial_0_1$Parse___123_emptyComments_95_33_125_());
}

// Parse.{tdef_491}

function Parse___123_tdef_95_491_125_($_0_lift, $_1_lift, $_2_lift){
    return $partial_8_9$Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Alternative_36_TParsecT_32_e_32_a_32_m_58__33__60__124__62__58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_127_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_128_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_133_125_()), $partial_0_4$Parse___123_tdef_95_447_125_()), null, $_1_lift, $_2_lift);
}

// Parse.{tdef_536}

function Parse___123_tdef_95_536_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return Prelude__Monad__TParsec__Types___64_Prelude__Monad__Monad_36_TParsecT_32_e_32_a_32_m_58__33__62__62__61__58_0(null, null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_127_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_128_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_133_125_()), $partial_0_4$Parse___123_tdef_95_447_125_()), $_2_lift, $_3_lift);
}

// Parse.{tdef_538}

function Parse___123_tdef_95_538_125_($_0_lift, $_1_lift){
    return ($_0_lift === $_1_lift);
}

// Parse.{tdef_539}

function Parse___123_tdef_95_539_125_($_0_lift, $_1_lift){
    
    if((((($_0_lift === $_1_lift)) ? 1|0 : 0|0) === 0)) {
        return true;
    } else {
        return false;
    }
}

// Parse.{tdef_540}

function Parse___123_tdef_95_540_125_($_0_lift, $_1_lift){
    return Data__Inspect__Data__Inspect___64_Data__Inspect__Inspect_36_SizedList_32_a_58_a_58__33_inspect_58_0_58_go_58_0(null, null, null, null, $_0_lift, $_1_lift, null);
}

// Parse.{tdef_706}

function Parse___123_tdef_95_706_125_($_0_lift){
    
    const $cg$3 = $_0_lift.$1;
    let $cg$2 = null;
    if(($cg$3.type === 0)) {
        $cg$2 = $HC_0_0$Prelude__Maybe__Nothing;
    } else {
        $cg$2 = Data__SortedMap__treeLookup(null, null, $cg$3.$1, null, $_0_lift.$2, $cg$3.$2);
    }
    
    
    if(($cg$2.type === 1)) {
        const $cg$6 = $cg$2.$1;
        let $cg$5 = null;
        $cg$5 = $cg$6.$1;
        const $cg$8 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Nat_58__33_decEq_58_0($cg$5, (new $JSRTS.jsbn.BigInteger(("0"))));
        if(($cg$8.type === 1)) {
            return $HC_0_0$Prelude__Maybe__Nothing;
        } else {
            const $cg$10 = $cg$2.$1;
            let $cg$9 = null;
            $cg$9 = $cg$10.$1;
            const $cg$12 = $cg$2.$1;
            let $cg$11 = null;
            $cg$11 = new $HC_2_0$Typedefs__TName($_0_lift.$2, $cg$12.$2);
            return new $HC_1_1$Prelude__Maybe__Just(new $HC_2_0$Builtins__MkDPair((new $JSRTS.jsbn.BigInteger(("0"))), new $HC_3_6$Typedefs__TApp($cg$9, $cg$11, $HC_0_0$Data__Vect__Nil)));
        }
    } else {
        return $HC_0_0$Prelude__Maybe__Nothing;
    }
}

// Parse.{tdef_982}

function Parse___123_tdef_95_982_125_($_0_lift, $_1_lift){
    
    const $cg$3 = $_1_lift.$2;
    return Typedefs__weakenTDef(null, $cg$3.$2, $_0_lift, $cg$3.$1);
}

// Parse.{tdef_983}

function Parse___123_tdef_95_983_125_($_0_lift){
    
    const $cg$3 = $_0_lift.$2;
    let $cg$2 = null;
    $cg$2 = new $HC_2_1$Data__Vect___58__58_($cg$3.$1, Data__Vect__fromList(null, $cg$3.$2));
    const $cg$5 = Parse__toVMax(null, null, $cg$2);
    const $cg$7 = $_0_lift.$1;
    let $cg$6 = null;
    $cg$6 = $cg$7.$1;
    const $cg$9 = $_0_lift.$2;
    let $cg$8 = null;
    $cg$8 = $cg$9.$2;
    const $cg$11 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Nat_58__33_decEq_58_0($cg$6, Prelude__List__length(null, $cg$8).add((new $JSRTS.jsbn.BigInteger(("1")))));
    if(($cg$11.type === 1)) {
        return $HC_0_0$Prelude__Maybe__Nothing;
    } else {
        const $cg$13 = $_0_lift.$1;
        let $cg$12 = null;
        $cg$12 = $cg$13.$1;
        const $cg$15 = $_0_lift.$1;
        let $cg$14 = null;
        $cg$14 = $cg$15.$2;
        return new $HC_1_1$Prelude__Maybe__Just(new $HC_2_0$Builtins__MkDPair($cg$5.$1, new $HC_3_6$Typedefs__TApp($cg$12, $cg$14, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_1_2$Parse___123_tdef_95_982_125_($cg$5.$1), Parse__fromVMax_58_go_58_0(null, $cg$5.$1, null, null, null, null, Prelude__Nat__lteRefl($cg$5.$1), $cg$5.$2)))));
    }
}

// Parse.{tdef_1244}

function Parse___123_tdef_95_1244_125_($_0_lift, $_1_lift){
    
    return new $HC_2_0$Builtins__MkDPair($_1_lift.$1, new $HC_2_0$Typedefs__TName($_0_lift, $_1_lift.$2));
}

// Parse.{tdef_1245}

function Parse___123_tdef_95_1245_125_($_0_lift){
    
    const $cg$3 = $_0_lift.$1;
    let $cg$2 = null;
    if(($cg$3.type === 0)) {
        $cg$2 = $HC_0_0$Prelude__Maybe__Nothing;
    } else {
        $cg$2 = Data__SortedMap__treeLookup(null, null, $cg$3.$1, null, $_0_lift.$2, $cg$3.$2);
    }
    
    return Prelude__Functor__Prelude___64_Prelude__Functor__Functor_36_Maybe_58__33_map_58_0(null, null, $partial_1_2$Parse___123_tdef_95_1244_125_($_0_lift.$2), $cg$2);
}

// Parse.{tdef_1631}

function Parse___123_tdef_95_1631_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return TParsec__Combinators__nelist(null, null, null, new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $_2_lift)(Parse__ignorespaces(null, null, $partial_0_3$Parse___123_tdef_95_431_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $partial_0_1$Typedefs___123_apN_95_20_125_(), new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Parse___123_tdef_95_538_125_(), $partial_0_2$Parse___123_tdef_95_539_125_()), $partial_0_2$Parse___123_tdef_95_540_125_(), $_2_lift, $_0_lift($_2_lift)($_3_lift)));
}

// Parse.{tdef_1632}

function Parse___123_tdef_95_1632_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift){
    return $partial_10_11$TParsec__Combinators__andbind(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), null, $partial_9_12$TParsec__Combinators__guardM(null, null, null, null, new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $partial_0_1$Parse___123_tdef_95_1245_125_(), null, $partial_8_11$TParsec__Combinators__mand(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), null, Control__Monad__Trans__TParsec__Types___64_Control__Monad__Trans__MonadTrans_36_TParsecT_32_e_32_a_58__33_lift_58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_127_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_128_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_133_125_()), $partial_0_4$Parse___123_tdef_95_447_125_()), $partial_0_1$Backend__Utils___123_ifNotPresent_95_92_125_()), TParsec__Combinators__Chars__alphas(null, $partial_0_3$Parse___123_tdef_95_431_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $partial_0_1$Typedefs___123_apN_95_20_125_(), $partial_0_1$Typedefs___123_apN_95_20_125_(), new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Parse___123_tdef_95_538_125_(), $partial_0_2$Parse___123_tdef_95_539_125_()), $partial_0_2$Parse___123_tdef_95_540_125_(), $_0_lift))), $partial_1_4$Parse___123_tdef_95_1631_125_($_1_lift), $_4_lift, Prelude__Nat__lteTransitive(null, null, null, $_5_lift, null));
}

// Parse.{tdef_1636}

function Parse___123_tdef_95_1636_125_($_0_lift){
    return new $HC_2_0$Builtins__MkDPair((new $JSRTS.jsbn.BigInteger(("0"))), $HC_0_0$Typedefs__T0);
}

// Parse.{tdef_1750}

function Parse___123_tdef_95_1750_125_($_0_lift){
    return new $HC_2_0$Builtins__MkDPair((new $JSRTS.jsbn.BigInteger(("0"))), $HC_0_1$Typedefs__T1);
}

// Parse.{tdef_1861}

function Parse___123_tdef_95_1861_125_($_0_lift, $_1_lift, $_2_lift){
    return new $HC_2_3$Typedefs__TProd($_0_lift, $_2_lift);
}

// Parse.{tdef_1862}

function Parse___123_tdef_95_1862_125_($_0_lift, $_1_lift, $_2_lift){
    return new $HC_2_2$Typedefs__TSum($_0_lift, $_2_lift);
}

// Parse.{tdef_1866}

function Parse___123_tdef_95_1866_125_($_0_lift){
    return new $HC_2_0$Builtins__MkDPair($_0_lift.add((new $JSRTS.jsbn.BigInteger(("1")))), new $HC_1_4$Typedefs__TVar(Data__Fin__last($_0_lift)));
}

// Parse.{tdef_2462}

function Parse___123_tdef_95_2462_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    return Parse__ignorespaces(null, null, $partial_0_3$Parse___123_tdef_95_431_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $partial_0_1$Typedefs___123_apN_95_20_125_(), new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Parse___123_tdef_95_538_125_(), $partial_0_2$Parse___123_tdef_95_539_125_()), $partial_0_2$Parse___123_tdef_95_540_125_(), $_0_lift, TParsec__Combinators__Numbers__decimalNat(null, $partial_0_3$Parse___123_tdef_95_431_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $partial_0_1$Typedefs___123_apN_95_20_125_(), new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Parse___123_tdef_95_538_125_(), $partial_0_2$Parse___123_tdef_95_539_125_()), $partial_0_2$Parse___123_tdef_95_540_125_(), $_0_lift))($_3_lift)(Prelude__Nat__lteTransitive(null, null, null, $_4_lift, null));
}

// Parse.{tdef_2463}

function Parse___123_tdef_95_2463_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    return TParsec__Combinators__rand(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), null, null, Parse__ignorespaces(null, null, $partial_0_3$Parse___123_tdef_95_431_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $partial_0_1$Typedefs___123_apN_95_20_125_(), new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Parse___123_tdef_95_538_125_(), $partial_0_2$Parse___123_tdef_95_539_125_()), $partial_0_2$Parse___123_tdef_95_540_125_(), $_0_lift, TParsec__Combinators__Chars__string(null, $partial_0_3$Parse___123_tdef_95_431_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $partial_0_1$Typedefs___123_apN_95_20_125_(), new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Parse___123_tdef_95_538_125_(), $partial_0_2$Parse___123_tdef_95_539_125_()), $partial_0_2$Parse___123_tdef_95_540_125_(), "var", null, $_0_lift)), $partial_1_5$Parse___123_tdef_95_2462_125_($_0_lift))($_3_lift)(Prelude__Nat__lteTransitive(null, null, null, $_4_lift, null));
}

// Parse.{tdef_2467}

function Parse___123_tdef_95_2467_125_($_0_lift){
    
    const $cg$3 = $_0_lift.$2;
    return new $HC_2_0$Builtins__MkDPair($cg$3.$1, new $HC_2_0$Builtins__MkPair($_0_lift.$1, $cg$3.$2));
}

// Parse.{tdef_2468}

function Parse___123_tdef_95_2468_125_($_0_lift){
    
    const $cg$3 = $_0_lift.$2;
    const $cg$5 = $cg$3.$2;
    return new $HC_2_0$Builtins__MkPair($cg$5.$1, Typedefs__weakenTDef(null, $cg$5.$2, (new $JSRTS.jsbn.BigInteger(("1"))), Prelude__Nat__lteSuccRight(null, null, $cg$3.$1)));
}

// Parse.{tdef_2469}

function Parse___123_tdef_95_2469_125_($_0_lift, $_1_lift){
    
    const $cg$3 = $_1_lift.$2;
    const $cg$5 = $cg$3.$2;
    return new $HC_2_0$Builtins__MkPair($cg$5.$1, Typedefs__weakenTDef(null, $cg$5.$2, $_0_lift.add((new $JSRTS.jsbn.BigInteger(("1")))), $cg$3.$1));
}

// Parse.{tdef_2470}

function Parse___123_tdef_95_2470_125_($_0_lift){
    let $cg$1 = null;
    $cg$1 = new $HC_2_1$Data__Vect___58__58_($_0_lift.$1, Data__Vect__fromList(null, $_0_lift.$2));
    const $_11647_in = Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Parse___123_tdef_95_2467_125_(), $cg$1);
    const $cg$3 = Parse__toVMax(null, null, $_11647_in);
    
    if($cg$3.$1.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
        let $cg$5 = null;
        $cg$5 = $_0_lift.$2;
        return new $HC_2_0$Builtins__MkDPair((new $JSRTS.jsbn.BigInteger(("0"))), new $HC_2_5$Typedefs__TMu(Prelude__List__length(null, $cg$5).add((new $JSRTS.jsbn.BigInteger(("1")))), Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Parse___123_tdef_95_2468_125_(), Parse__fromVMax_58_go_58_0(null, (new $JSRTS.jsbn.BigInteger(("0"))), null, null, null, null, Prelude__Nat__lteRefl((new $JSRTS.jsbn.BigInteger(("0")))), $cg$3.$2))));
    } else {
        const $_11666_in = $cg$3.$1.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
        let $cg$6 = null;
        $cg$6 = $_0_lift.$2;
        return new $HC_2_0$Builtins__MkDPair($_11666_in, new $HC_2_5$Typedefs__TMu(Prelude__List__length(null, $cg$6).add((new $JSRTS.jsbn.BigInteger(("1")))), Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_1_2$Parse___123_tdef_95_2469_125_($_11666_in), Parse__fromVMax_58_go_58_0(null, $_11666_in.add((new $JSRTS.jsbn.BigInteger(("1")))), null, null, null, null, Prelude__Nat__lteRefl($_11666_in.add((new $JSRTS.jsbn.BigInteger(("1"))))), $cg$3.$2))));
    }
}

// Parse.{tdef_3437}

function Parse___123_tdef_95_3437_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift, $_7_lift){
    return $_0_lift($_1_lift)($_2_lift)($_6_lift)(Prelude__Nat__lteTransitive(null, null, null, $_7_lift, null));
}

// Parse.{tdef_3438}

function Parse___123_tdef_95_3438_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift){
    return $partial_10_11$TParsec__Combinators__andbind(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), null, Parse__ignorespaces(null, null, $partial_0_3$Parse___123_tdef_95_431_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $partial_0_1$Typedefs___123_apN_95_20_125_(), new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Parse___123_tdef_95_538_125_(), $partial_0_2$Parse___123_tdef_95_539_125_()), $partial_0_2$Parse___123_tdef_95_540_125_(), $_0_lift, TParsec__Combinators__Chars__alphas(null, $partial_0_3$Parse___123_tdef_95_431_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $partial_0_1$Typedefs___123_apN_95_20_125_(), $partial_0_1$Typedefs___123_apN_95_20_125_(), new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Parse___123_tdef_95_538_125_(), $partial_0_2$Parse___123_tdef_95_539_125_()), $partial_0_2$Parse___123_tdef_95_540_125_(), $_0_lift)), $partial_3_8$Parse___123_tdef_95_3437_125_($_1_lift, $_0_lift, $_2_lift), $_5_lift, Prelude__Nat__lteTransitive(null, null, null, $_6_lift, null));
}

// Parse.{tdef_3439}

function Parse___123_tdef_95_3439_125_($_0_lift, $_1_lift, $_2_lift){
    return TParsec__Combinators__nelist(null, null, null, new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $_1_lift)(Parse__ignorespaces(null, null, $partial_0_3$Parse___123_tdef_95_431_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $partial_0_1$Typedefs___123_apN_95_20_125_(), new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Parse___123_tdef_95_538_125_(), $partial_0_2$Parse___123_tdef_95_539_125_()), $partial_0_2$Parse___123_tdef_95_540_125_(), $_1_lift, TParsec__Combinators__Chars__parens(null, null, $partial_0_3$Parse___123_tdef_95_431_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $partial_0_1$Typedefs___123_apN_95_20_125_(), new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Parse___123_tdef_95_538_125_(), $partial_0_2$Parse___123_tdef_95_539_125_()), $partial_0_2$Parse___123_tdef_95_540_125_(), $_1_lift, $partial_3_7$Parse___123_tdef_95_3438_125_($_1_lift, $_0_lift, $_2_lift))));
}

// Parse.{tdef_3440}

function Parse___123_tdef_95_3440_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift){
    return TParsec__Combinators__rand(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), null, null, Parse__ignorespaces(null, null, $partial_0_3$Parse___123_tdef_95_431_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $partial_0_1$Typedefs___123_apN_95_20_125_(), new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Parse___123_tdef_95_538_125_(), $partial_0_2$Parse___123_tdef_95_539_125_()), $partial_0_2$Parse___123_tdef_95_540_125_(), $_0_lift, TParsec__Combinators__Chars__string(null, $partial_0_3$Parse___123_tdef_95_431_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $partial_0_1$Typedefs___123_apN_95_20_125_(), new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Parse___123_tdef_95_538_125_(), $partial_0_2$Parse___123_tdef_95_539_125_()), $partial_0_2$Parse___123_tdef_95_540_125_(), "mu", null, $_0_lift)), $partial_1_3$Parse___123_tdef_95_3439_125_($_1_lift))($_4_lift)(Prelude__Nat__lteTransitive(null, null, null, $_5_lift, null));
}

// Parse.{tdef_3441}

function Parse___123_tdef_95_3441_125_($_0_lift, $_1_lift){
    return Parse__ignorespaces(null, null, $partial_0_3$Parse___123_tdef_95_431_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $partial_0_1$Typedefs___123_apN_95_20_125_(), new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Parse___123_tdef_95_538_125_(), $partial_0_2$Parse___123_tdef_95_539_125_()), $partial_0_2$Parse___123_tdef_95_540_125_(), $_0_lift, TParsec__Combinators__alts(null, null, null, new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), null, new $HC_2_1$Prelude__List___58__58_($partial_9_12$TParsec__Combinators__guardM(null, null, null, null, new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $partial_0_1$Parse___123_tdef_95_706_125_(), null, $partial_8_11$TParsec__Combinators__mand(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), null, Control__Monad__Trans__TParsec__Types___64_Control__Monad__Trans__MonadTrans_36_TParsecT_32_e_32_a_58__33_lift_58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_127_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_128_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_133_125_()), $partial_0_4$Parse___123_tdef_95_447_125_()), $partial_0_1$Backend__Utils___123_ifNotPresent_95_92_125_()), TParsec__Combinators__Chars__alphas(null, $partial_0_3$Parse___123_tdef_95_431_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $partial_0_1$Typedefs___123_apN_95_20_125_(), $partial_0_1$Typedefs___123_apN_95_20_125_(), new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Parse___123_tdef_95_538_125_(), $partial_0_2$Parse___123_tdef_95_539_125_()), $partial_0_2$Parse___123_tdef_95_540_125_(), $_0_lift))), new $HC_2_1$Prelude__List___58__58_($partial_9_12$TParsec__Combinators__guardM(null, null, null, null, new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $partial_0_1$Parse___123_tdef_95_983_125_(), null, TParsec__Combinators__Chars__parens(null, null, $partial_0_3$Parse___123_tdef_95_431_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $partial_0_1$Typedefs___123_apN_95_20_125_(), new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Parse___123_tdef_95_538_125_(), $partial_0_2$Parse___123_tdef_95_539_125_()), $partial_0_2$Parse___123_tdef_95_540_125_(), $_0_lift, $partial_2_6$Parse___123_tdef_95_1632_125_($_0_lift, $_1_lift))), new $HC_2_1$Prelude__List___58__58_($partial_8_11$TParsec__Combinators__map(null, null, null, null, $partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_1$Parse___123_tdef_95_1636_125_(), null, TParsec__Combinators__Chars__string(null, $partial_0_3$Parse___123_tdef_95_431_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $partial_0_1$Typedefs___123_apN_95_20_125_(), new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Parse___123_tdef_95_538_125_(), $partial_0_2$Parse___123_tdef_95_539_125_()), $partial_0_2$Parse___123_tdef_95_540_125_(), "0", null, $_0_lift)), new $HC_2_1$Prelude__List___58__58_($partial_8_11$TParsec__Combinators__map(null, null, null, null, $partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_1$Parse___123_tdef_95_1750_125_(), null, TParsec__Combinators__Chars__string(null, $partial_0_3$Parse___123_tdef_95_431_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $partial_0_1$Typedefs___123_apN_95_20_125_(), new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Parse___123_tdef_95_538_125_(), $partial_0_2$Parse___123_tdef_95_539_125_()), $partial_0_2$Parse___123_tdef_95_540_125_(), "1", null, $_0_lift)), new $HC_2_1$Prelude__List___58__58_(Parse__tdef_58_nary_58_0(null, $_0_lift, $_1_lift, "*", $partial_0_3$Parse___123_tdef_95_1861_125_()), new $HC_2_1$Prelude__List___58__58_(Parse__tdef_58_nary_58_0(null, $_0_lift, $_1_lift, "+", $partial_0_3$Parse___123_tdef_95_1862_125_()), new $HC_2_1$Prelude__List___58__58_($partial_8_11$TParsec__Combinators__map(null, null, null, null, $partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_1$Parse___123_tdef_95_1866_125_(), null, TParsec__Combinators__Chars__parens(null, null, $partial_0_3$Parse___123_tdef_95_431_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $partial_0_1$Typedefs___123_apN_95_20_125_(), new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Parse___123_tdef_95_538_125_(), $partial_0_2$Parse___123_tdef_95_539_125_()), $partial_0_2$Parse___123_tdef_95_540_125_(), $_0_lift, $partial_1_5$Parse___123_tdef_95_2463_125_($_0_lift))), new $HC_2_1$Prelude__List___58__58_($partial_8_11$TParsec__Combinators__map(null, null, null, null, $partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_1$Parse___123_tdef_95_2470_125_(), null, TParsec__Combinators__Chars__parens(null, null, $partial_0_3$Parse___123_tdef_95_431_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $partial_0_1$Typedefs___123_apN_95_20_125_(), new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Parse___123_tdef_95_538_125_(), $partial_0_2$Parse___123_tdef_95_539_125_()), $partial_0_2$Parse___123_tdef_95_540_125_(), $_0_lift, $partial_2_6$Parse___123_tdef_95_3440_125_($_0_lift, $_1_lift))), $HC_0_0$Prelude__List__Nil))))))))));
}

// Parse.{tnamed_4348}

function Parse___123_tnamed_95_4348_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift){
    return Parse__ignorespaces(null, null, $partial_0_3$Parse___123_tdef_95_431_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $partial_0_1$Typedefs___123_apN_95_20_125_(), new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Parse___123_tdef_95_538_125_(), $partial_0_2$Parse___123_tdef_95_539_125_()), $partial_0_2$Parse___123_tdef_95_540_125_(), $_0_lift, Parse__tdef($_0_lift))($_4_lift)(Prelude__Nat__lteTransitive(null, null, null, $_5_lift, null));
}

// Parse.{tnamed_4349}

function Parse___123_tnamed_95_4349_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    return $partial_10_11$TParsec__Combinators__andbind(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), null, Parse__ignorespaces(null, null, $partial_0_3$Parse___123_tdef_95_431_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $partial_0_1$Typedefs___123_apN_95_20_125_(), new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Parse___123_tdef_95_538_125_(), $partial_0_2$Parse___123_tdef_95_539_125_()), $partial_0_2$Parse___123_tdef_95_540_125_(), $_0_lift, TParsec__Combinators__Chars__alphas(null, $partial_0_3$Parse___123_tdef_95_431_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $partial_0_1$Typedefs___123_apN_95_20_125_(), $partial_0_1$Typedefs___123_apN_95_20_125_(), new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Parse___123_tdef_95_538_125_(), $partial_0_2$Parse___123_tdef_95_539_125_()), $partial_0_2$Parse___123_tdef_95_540_125_(), $_0_lift)), $partial_1_6$Parse___123_tnamed_95_4348_125_($_0_lift), $_3_lift, Prelude__Nat__lteTransitive(null, null, null, $_4_lift, null));
}

// Parse.{tnamed_4350}

function Parse___123_tnamed_95_4350_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    return TParsec__Combinators__rand(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), null, null, Parse__ignorespaces(null, null, $partial_0_3$Parse___123_tdef_95_431_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $partial_0_1$Typedefs___123_apN_95_20_125_(), new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Parse___123_tdef_95_538_125_(), $partial_0_2$Parse___123_tdef_95_539_125_()), $partial_0_2$Parse___123_tdef_95_540_125_(), $_0_lift, TParsec__Combinators__Chars__string(null, $partial_0_3$Parse___123_tdef_95_431_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $partial_0_1$Typedefs___123_apN_95_20_125_(), new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Parse___123_tdef_95_538_125_(), $partial_0_2$Parse___123_tdef_95_539_125_()), $partial_0_2$Parse___123_tdef_95_540_125_(), "name", null, $_0_lift)), $partial_1_5$Parse___123_tnamed_95_4349_125_($_0_lift))($_3_lift)(Prelude__Nat__lteTransitive(null, null, null, $_4_lift, null));
}

// Parse.{tnamed_4385}

function Parse___123_tnamed_95_4385_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    return new $HC_2_0$Builtins__MkPair($HC_0_0$MkUnit, Data__SortedMap__insert(null, null, $_0_lift, new $HC_2_0$Builtins__MkDPair($_1_lift, $_2_lift), $_3_lift));
}

// Parse.{tnamed_4399}

function Parse___123_tnamed_95_4399_125_($_0_lift){
    
    const $cg$3 = $_0_lift.$2;
    return Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0(null, null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_127_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_128_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_133_125_()), $partial_0_4$Parse___123_tdef_95_447_125_()), Prelude__Functor__TParsec__Types___64_Prelude__Functor__Functor_36_TParsecT_32_e_32_a_32_m_58__33_map_58_0(null, null, null, null, null, $partial_0_4$Backend__Haskell___123_makeDefs_95_127_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), Control__Monad__Trans__TParsec__Types___64_Control__Monad__Trans__MonadTrans_36_TParsecT_32_e_32_a_58__33_lift_58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_127_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_128_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_133_125_()), $partial_0_4$Parse___123_tdef_95_447_125_()), $partial_7_8$Prelude__Monad__Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), $partial_0_3$Backend__Utils___123_ifNotPresent_95_88_125_()), $partial_0_4$Backend__Utils___123_ifNotPresent_95_91_125_()), $partial_0_1$Backend__Utils___123_ifNotPresent_95_92_125_(), $partial_3_5$Parse___123_tnamed_95_4385_125_($_0_lift.$1, $cg$3.$1, $cg$3.$2)))), $partial_6_7$Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33_pure_58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_127_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_128_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_133_125_()), $partial_0_4$Parse___123_tdef_95_447_125_()), new $HC_2_0$Builtins__MkDPair($cg$3.$1, new $HC_2_0$Typedefs__TName($_0_lift.$1, $cg$3.$2))));
}

// Parse.{tnamedRec_4403}

function Parse___123_tnamedRec_95_4403_125_($_0_lift){
    
    const $cg$3 = $_0_lift.$2;
    if(($cg$3.type === 1)) {
        return $cg$3.$1;
    } else {
        return $_0_lift.$1;
    }
}

// Parse.{tnamedRec_4510}

function Parse___123_tnamedRec_95_4510_125_($_0_lift, $_1_lift){
    return $partial_8_11$TParsec__Combinators__map(null, null, null, null, $partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_1$Parse___123_tnamedRec_95_4403_125_(), null, $partial_9_12$TParsec__Combinators__andoptbind(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), null, Parse__tnamed($_0_lift), $partial_1_2$TParsec__Combinators__Numbers___123_decimalDigit_95_25_125_($_1_lift)));
}

// Text.PrettyPrint.WL.Core.{toString_4511}

function Text__PrettyPrint__WL__Core___123_toString_95_4511_125_($_0_lift){
    return $HC_0_0$Text__PrettyPrint__WL__Core__PrettyDoc__Empty;
}

// TParsec.Combinators.Chars.{withSpaces_4512}

function TParsec__Combinators__Chars___123_withSpaces_95_4512_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift, $_7_lift, $_8_lift, $_9_lift, $_10_lift){
    return TParsec__Combinators__nelist(null, null, null, $_0_lift, $_1_lift, $_2_lift)(TParsec__Combinators__Chars__space(null, $_3_lift, $_0_lift, $_1_lift, $_4_lift, $_5_lift, $_6_lift, null))($_9_lift)(Prelude__Nat__lteTransitive(null, null, null, $_10_lift, null));
}

// Prelude.Applicative.{TParsec.Types.@Prelude.Applicative.Alternative$TParsecT e a m:!<|>:0_lam_5272}

function Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Alternative_36_TParsecT_32_e_32_a_32_m_58__33__60__124__62__58_0_95_lam_95_5272_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    
    if(($_3_lift.type === 1)) {
        return $_0_lift($_1_lift);
    } else {
        
        const $cg$4 = $_2_lift.$1;
        return $cg$4.$2(null)($_3_lift);
    }
}

// Prelude.Applicative.{TParsec.Result.@Prelude.Applicative.Applicative$ResultT e m:!<*>:0_lam_5273}

function Prelude__Applicative___123_TParsec__Result___64_Prelude__Applicative__Applicative_36_ResultT_32_e_32_m_58__33__60__42__62__58_0_95_lam_95_5273_125_($_0_lift, $_1_lift, $_2_lift){
    
    const $cg$3 = $_0_lift.$1;
    return $cg$3.$2(null)(Prelude__Applicative__TParsec__Result___64_Prelude__Applicative__Applicative_36_Result_32_e_58__33__60__42__62__58_0(null, null, null, $_1_lift, $_2_lift));
}

// Prelude.Applicative.{TParsec.Result.@Prelude.Applicative.Applicative$ResultT e m:!<*>:0_lam_5274}

function Prelude__Applicative___123_TParsec__Result___64_Prelude__Applicative__Applicative_36_ResultT_32_e_32_m_58__33__60__42__62__58_0_95_lam_95_5274_125_($_0_lift, $_1_lift, $_2_lift){
    
    return $_0_lift.$2(null)(null)($_1_lift)($partial_2_3$Prelude__Applicative___123_TParsec__Result___64_Prelude__Applicative__Applicative_36_ResultT_32_e_32_m_58__33__60__42__62__58_0_95_lam_95_5273_125_($_0_lift, $_2_lift));
}

// Prelude.Applicative.{Control.Monad.State.@Prelude.Applicative.Applicative$StateT stateType f:!<*>:0_lam_5275}

function Prelude__Applicative___123_Control__Monad__State___64_Prelude__Applicative__Applicative_36_StateT_32_stateType_32_f_58__33__60__42__62__58_0_95_lam_95_5275_125_($_0_lift, $_1_lift, $_2_lift){
    
    
    const $cg$4 = $_0_lift.$1;
    return $cg$4.$2(null)(new $HC_2_0$Builtins__MkPair($_1_lift($_2_lift.$1), $_2_lift.$2));
}

// Prelude.Applicative.{Control.Monad.State.@Prelude.Applicative.Applicative$StateT stateType f:!<*>:0_lam_5276}

function Prelude__Applicative___123_Control__Monad__State___64_Prelude__Applicative__Applicative_36_StateT_32_stateType_32_f_58__33__60__42__62__58_0_95_lam_95_5276_125_($_0_lift, $_1_lift, $_2_lift){
    
    
    return $_0_lift.$2(null)(null)($_1_lift($_2_lift.$2))($partial_2_3$Prelude__Applicative___123_Control__Monad__State___64_Prelude__Applicative__Applicative_36_StateT_32_stateType_32_f_58__33__60__42__62__58_0_95_lam_95_5275_125_($_0_lift, $_2_lift.$1));
}

// Prelude.Applicative.{TParsec.Types.@Prelude.Applicative.Applicative$TParsecT e a m:!<*>:0_lam_5277}

function Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5277_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    let $cg$1 = null;
    const $cg$3 = $_0_lift.$1;
    $cg$1 = $cg$3.$1;
    return Prelude__Functor__TParsec__Result___64_Prelude__Functor__Functor_36_ResultT_32_e_32_m_58__33_map_58_0(null, null, null, null, $cg$1, $_3_lift, $_4_lift);
}

// Prelude.Applicative.{TParsec.Types.@Prelude.Applicative.Applicative$TParsecT e a m:!<*>:0_lam_5278}

function Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5278_125_($_0_lift, $_1_lift, $_2_lift){
    
    const $cg$3 = $_0_lift.$1;
    return $cg$3.$2(null)(new $HC_1_2$TParsec__Result__Value($_2_lift));
}

// Prelude.Applicative.{TParsec.Types.@Prelude.Applicative.Applicative$TParsecT e a m:!<*>:0_lam_5279}

function Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5279_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    return Prelude__Applicative__TParsec__Result___64_Prelude__Applicative__Applicative_36_ResultT_32_e_32_m_58__33__60__42__62__58_0(null, null, null, null, $_0_lift, $_3_lift, $_4_lift);
}

// Prelude.Applicative.{TParsec.Types.@Prelude.Applicative.Applicative$TParsecT e a m:!<*>:0_lam_5280}

function Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5280_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    return Prelude__Monad__TParsec__Result___64_Prelude__Monad__Monad_36_ResultT_32_e_32_m_58__33__62__62__61__58_0(null, null, null, null, $_0_lift, $_3_lift, $_4_lift);
}

// Prelude.Functor.{TParsec.Result.@Prelude.Functor.Functor$ResultT e m:!map:0_lam_5281}

function Prelude__Functor___123_TParsec__Result___64_Prelude__Functor__Functor_36_ResultT_32_e_32_m_58__33_map_58_0_95_lam_95_5281_125_($_0_lift, $_1_lift){
    return Prelude__Functor__TParsec__Result___64_Prelude__Functor__Functor_36_Result_32_e_58__33_map_58_0(null, null, null, $_0_lift, $_1_lift);
}

// Prelude.Functor.{Control.Monad.State.@Prelude.Functor.Functor$StateT stateType f:!map:0_lam_5282}

function Prelude__Functor___123_Control__Monad__State___64_Prelude__Functor__Functor_36_StateT_32_stateType_32_f_58__33_map_58_0_95_lam_95_5282_125_($_0_lift, $_1_lift){
    
    return new $HC_2_0$Builtins__MkPair($_0_lift($_1_lift.$1), $_1_lift.$2);
}

// Prelude.Functor.{TParsec.Types.@Prelude.Functor.Functor$TParsecT e a m:!map:0_lam_5283}

function Prelude__Functor___123_TParsec__Types___64_Prelude__Functor__Functor_36_TParsecT_32_e_32_a_32_m_58__33_map_58_0_95_lam_95_5283_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    return Prelude__Functor__TParsec__Result___64_Prelude__Functor__Functor_36_ResultT_32_e_32_m_58__33_map_58_0(null, null, null, null, $_0_lift, $_3_lift, $_4_lift);
}

// Prelude.Monad.{TParsec.Result.@Prelude.Monad.Monad$ResultT e m:!>>=:0_lam_5284}

function Prelude__Monad___123_TParsec__Result___64_Prelude__Monad__Monad_36_ResultT_32_e_32_m_58__33__62__62__61__58_0_95_lam_95_5284_125_($_0_lift, $_1_lift, $_2_lift){
    
    if(($_2_lift.type === 0)) {
        
        const $cg$7 = $_0_lift.$1;
        return $cg$7.$2(null)(new $HC_1_0$TParsec__Result__HardFail($_2_lift.$1));
    } else if(($_2_lift.type === 1)) {
        
        const $cg$4 = $_0_lift.$1;
        return $cg$4.$2(null)(new $HC_1_1$TParsec__Result__SoftFail($_2_lift.$1));
    } else {
        return $_1_lift($_2_lift.$1);
    }
}

// Prelude.Monad.{Control.Monad.State.@Prelude.Monad.Monad$StateT stateType m:!>>=:0_lam_5285}

function Prelude__Monad___123_Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0_95_lam_95_5285_125_($_0_lift, $_1_lift){
    
    return $_0_lift($_1_lift.$1)($_1_lift.$2);
}

// TParsec.Running.{TParsec.Running.@TParsec.Running.MonadRun$ResultT e m:!runMonad:0_lam_5290}

function TParsec__Running___123_TParsec__Running___64_TParsec__Running__MonadRun_36_ResultT_32_e_32_m_58__33_runMonad_58_0_95_lam_95_5290_125_($_0_lift, $_1_lift){
    let $cg$1 = null;
    if(($_0_lift.type === 0)) {
        $cg$1 = $HC_0_0$Prelude__List__Nil;
    } else if(($_0_lift.type === 1)) {
        $cg$1 = $HC_0_0$Prelude__List__Nil;
    } else {
        $cg$1 = new $HC_2_1$Prelude__List___58__58_($_0_lift.$1, $HC_0_0$Prelude__List__Nil);
    }
    
    return Prelude__List___43__43_(null, $cg$1, $_1_lift);
}

// TParsec.Running.{Parse.@TParsec.Running.MonadRun$StateT PState Identity:!runMonad:0_lam_5293}

function TParsec__Running___123_Parse___64_TParsec__Running__MonadRun_36_StateT_32_PState_32_Identity_58__33_runMonad_58_0_95_lam_95_5293_125_($_0_lift, $_1_lift){
    return Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_String_58__33_compare_58_0($_0_lift, $_1_lift);
}

// TParsec.Running.{Parse.@TParsec.Running.MonadRun$StateT PState Identity:!runMonad:0_lam_5294}

function TParsec__Running___123_Parse___64_TParsec__Running__MonadRun_36_StateT_32_PState_32_Identity_58__33_runMonad_58_0_95_lam_95_5294_125_($_0_lift, $_1_lift){
    
    if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_String_58__33_compare_58_0($_0_lift, $_1_lift) < 0)) {
        return true;
    } else {
        return ($_0_lift == $_1_lift);
    }
}

// TParsec.Running.{TParsec.Running.@TParsec.Running.MonadRun$TParsecT e a m:!runMonad:0_lam_5295}

function TParsec__Running___123_TParsec__Running___64_TParsec__Running__MonadRun_36_TParsecT_32_e_32_a_32_m_58__33_runMonad_58_0_95_lam_95_5295_125_($_0_lift){
    
    return $_0_lift.$1;
}

// Control.Monad.Trans.{TParsec.Result.@Control.Monad.Trans.MonadTrans$ResultT e:!lift:0_lam_5296}

function Control__Monad__Trans___123_TParsec__Result___64_Control__Monad__Trans__MonadTrans_36_ResultT_32_e_58__33_lift_58_0_95_lam_95_5296_125_($_0_lift){
    return new $HC_1_2$TParsec__Result__Value($_0_lift);
}

// Control.Monad.Trans.{Control.Monad.State.@Control.Monad.Trans.MonadTrans$StateT stateType:!lift:0_lam_5297}

function Control__Monad__Trans___123_Control__Monad__State___64_Control__Monad__Trans__MonadTrans_36_StateT_32_stateType_58__33_lift_58_0_95_lam_95_5297_125_($_0_lift, $_1_lift, $_2_lift){
    
    const $cg$3 = $_0_lift.$1;
    return $cg$3.$2(null)(new $HC_2_0$Builtins__MkPair($_2_lift, $_1_lift));
}

// Control.Monad.Trans.{TParsec.Types.@Control.Monad.Trans.MonadTrans$TParsecT e a:!lift:0_lam_5298}

function Control__Monad__Trans___123_TParsec__Types___64_Control__Monad__Trans__MonadTrans_36_TParsecT_32_e_32_a_58__33_lift_58_0_95_lam_95_5298_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    let $cg$1 = null;
    const $cg$3 = $_0_lift.$1;
    $cg$1 = $cg$3.$1;
    return Prelude__Functor__TParsec__Result___64_Prelude__Functor__Functor_36_ResultT_32_e_32_m_58__33_map_58_0(null, null, null, null, $cg$1, $_3_lift, $_4_lift);
}

// Control.Monad.Trans.{TParsec.Types.@Control.Monad.Trans.MonadTrans$TParsecT e a:!lift:0_lam_5299}

function Control__Monad__Trans___123_TParsec__Types___64_Control__Monad__Trans__MonadTrans_36_TParsecT_32_e_32_a_58__33_lift_58_0_95_lam_95_5299_125_($_0_lift, $_1_lift, $_2_lift){
    
    const $cg$3 = $_0_lift.$1;
    return $cg$3.$2(null)(new $HC_1_2$TParsec__Result__Value($_2_lift));
}

// Prelude.Traversable.{Data.Vect.@Prelude.Traversable.Traversable$Vect n:!traverse:0_lam_5303}

function Prelude__Traversable___123_Data__Vect___64_Prelude__Traversable__Traversable_36_Vect_32_n_58__33_traverse_58_0_95_lam_95_5303_125_($_0_lift, $_1_lift){
    return new $HC_2_1$Data__Vect___58__58_($_0_lift, $_1_lift);
}

// Prelude.Applicative.TParsec.Types.TParsecT e a m implementation of Prelude.Applicative.Alternative, method <|>

function Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Alternative_36_TParsecT_32_e_32_a_32_m_58__33__60__124__62__58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_pos){
    
    return $_4_arg.$2(null)(null)($_6_arg($_8_pos))($partial_3_4$Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Alternative_36_TParsecT_32_e_32_a_32_m_58__33__60__124__62__58_0_95_lam_95_5272_125_($_7_arg, $_8_pos, $_4_arg));
}

// Prelude.Applicative.TParsec.Types.TParsecT e a m implementation of Prelude.Applicative.Alternative, method empty

function Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Alternative_36_TParsecT_32_e_32_a_32_m_58__33_empty_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_22_in){
    
    const $cg$3 = $_4_arg.$1;
    return $cg$3.$2(null)(new $HC_1_1$TParsec__Result__SoftFail($_5_arg($_22_in)));
}

// Prelude.Applicative.Prelude.Maybe implementation of Prelude.Applicative.Applicative, method <*>

function Prelude__Applicative__Prelude___64_Prelude__Applicative__Applicative_36_Maybe_58__33__60__42__62__58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    if(($_3_arg.type === 1)) {
        
        if(($_2_arg.type === 1)) {
            return new $HC_1_1$Prelude__Maybe__Just($_2_arg.$1($_3_arg.$1));
        } else {
            return $HC_0_0$Prelude__Maybe__Nothing;
        }
    } else {
        return $HC_0_0$Prelude__Maybe__Nothing;
    }
}

// Prelude.Applicative.TParsec.Result.Result e implementation of Prelude.Applicative.Applicative, method <*>

function Prelude__Applicative__TParsec__Result___64_Prelude__Applicative__Applicative_36_Result_32_e_58__33__60__42__62__58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    
    if(($_3_arg.type === 0)) {
        return $_3_arg;
    } else if(($_3_arg.type === 1)) {
        return $_3_arg;
    } else {
        
        if(($_4_arg.type === 0)) {
            return $_4_arg;
        } else if(($_4_arg.type === 1)) {
            return $_4_arg;
        } else {
            
            return new $HC_1_2$TParsec__Result__Value($_3_arg.$1($_4_arg.$1));
        }
    }
}

// Prelude.Applicative.TParsec.Result.ResultT e m implementation of Prelude.Applicative.Applicative, method <*>

function Prelude__Applicative__TParsec__Result___64_Prelude__Applicative__Applicative_36_ResultT_32_e_32_m_58__33__60__42__62__58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg){
    
    return $_4_arg.$2(null)(null)($_5_arg)($partial_2_3$Prelude__Applicative___123_TParsec__Result___64_Prelude__Applicative__Applicative_36_ResultT_32_e_32_m_58__33__60__42__62__58_0_95_lam_95_5274_125_($_4_arg, $_6_arg));
}

// Prelude.Applicative.Control.Monad.State.StateT stateType f implementation of Prelude.Applicative.Applicative, method <*>

function Prelude__Applicative__Control__Monad__State___64_Prelude__Applicative__Applicative_36_StateT_32_stateType_32_f_58__33__60__42__62__58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_st){
    
    return $_4_arg.$2(null)(null)($_5_arg($_7_st))($partial_2_3$Prelude__Applicative___123_Control__Monad__State___64_Prelude__Applicative__Applicative_36_StateT_32_stateType_32_f_58__33__60__42__62__58_0_95_lam_95_5276_125_($_4_arg, $_6_arg));
}

// Prelude.Applicative.TParsec.Types.TParsecT e a m implementation of Prelude.Applicative.Applicative, method <*>

function Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    return $partial_7_8$Prelude__Applicative__Control__Monad__State___64_Prelude__Applicative__Applicative_36_StateT_32_stateType_32_f_58__33__60__42__62__58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_1_5$Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5277_125_($_5_arg), $partial_1_3$Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5278_125_($_5_arg), $partial_1_5$Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5279_125_($_5_arg)), $partial_1_5$Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5280_125_($_5_arg)), $_6_arg, $_7_arg);
}

// Prelude.Applicative.TParsec.Types.TParsecT e a m implementation of Prelude.Applicative.Applicative, method pure

function Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33_pure_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_st){
    
    const $cg$3 = $_4_arg.$1;
    return $cg$3.$2(null)(new $HC_1_2$TParsec__Result__Value(new $HC_2_0$Builtins__MkPair($_5_arg, $_6_st)));
}

// Backend.Backend.JSON.JSONDef, JSON implementation of Backend.CodegenInterdep, method sourceCode

function Backend__Backend__JSON___64_Backend__CodegenInterdep_36_JSONDef_58_JSON_58__33_sourceCode_58_0($_0_arg, $_1_arg){
    let $cg$1 = null;
    if((((((Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $partial_0_2$prim_95__95_strCons(), "", Prelude__List__replicate(null, (new $JSRTS.jsbn.BigInteger(("0"))), " ")) + Language__JSON__Data__format_58_formatValue_58_0(null, null, null, (new $JSRTS.jsbn.BigInteger(("0"))), (new $JSRTS.jsbn.BigInteger(("2"))), Backend__JSON__makeSchema($_0_arg, $_1_arg))) == "")) ? 1|0 : 0|0) === 0)) {
        $cg$1 = true;
    } else {
        $cg$1 = false;
    }
    
    const $cg$3 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$1, true);
    let $cg$2 = null;
    if(($cg$3.type === 1)) {
        $cg$2 = $HC_0_0$Prelude__List__Nil;
    } else {
        let $cg$4 = null;
        if((((((Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $partial_0_2$prim_95__95_strCons(), "", Prelude__List__replicate(null, (new $JSRTS.jsbn.BigInteger(("0"))), " ")) + Language__JSON__Data__format_58_formatValue_58_0(null, null, null, (new $JSRTS.jsbn.BigInteger(("0"))), (new $JSRTS.jsbn.BigInteger(("2"))), Backend__JSON__makeSchema($_0_arg, $_1_arg))).slice(1) == "")) ? 1|0 : 0|0) === 0)) {
            $cg$4 = true;
        } else {
            $cg$4 = false;
        }
        
        const $cg$6 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$4, true);
        let $cg$5 = null;
        if(($cg$6.type === 1)) {
            $cg$5 = $HC_0_0$Prelude__Strings__StrNil;
        } else {
            $cg$5 = new $HC_2_1$Prelude__Strings__StrCons((Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $partial_0_2$prim_95__95_strCons(), "", Prelude__List__replicate(null, (new $JSRTS.jsbn.BigInteger(("0"))), " ")) + Language__JSON__Data__format_58_formatValue_58_0(null, null, null, (new $JSRTS.jsbn.BigInteger(("0"))), (new $JSRTS.jsbn.BigInteger(("2"))), Backend__JSON__makeSchema($_0_arg, $_1_arg))).slice(1)[0], (Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $partial_0_2$prim_95__95_strCons(), "", Prelude__List__replicate(null, (new $JSRTS.jsbn.BigInteger(("0"))), " ")) + Language__JSON__Data__format_58_formatValue_58_0(null, null, null, (new $JSRTS.jsbn.BigInteger(("0"))), (new $JSRTS.jsbn.BigInteger(("2"))), Backend__JSON__makeSchema($_0_arg, $_1_arg))).slice(1).slice(1));
        }
        
        $cg$2 = new $HC_2_1$Prelude__List___58__58_((Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $partial_0_2$prim_95__95_strCons(), "", Prelude__List__replicate(null, (new $JSRTS.jsbn.BigInteger(("0"))), " ")) + Language__JSON__Data__format_58_formatValue_58_0(null, null, null, (new $JSRTS.jsbn.BigInteger(("0"))), (new $JSRTS.jsbn.BigInteger(("2"))), Backend__JSON__makeSchema($_0_arg, $_1_arg)))[0], _95_Prelude__Strings__unpack_95_with_95_36(null, $cg$5));
    }
    
    return Text__PrettyPrint__WL__Combinators__literal_58_mkLiteral_58_0(null, $cg$2);
}

// Decidable.Equality.Decidable.Equality.Bool implementation of Decidable.Equality.DecEq, method decEq

function Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($_0_arg, $_1_arg){
    
    if($_1_arg) {
        
        if($_0_arg) {
            return new $HC_1_0$Prelude__Basics__Yes($HC_0_0$Refl);
        } else {
            return $HC_0_1$Prelude__Basics__No;
        }
    } else {
        
        if($_0_arg) {
            return $HC_0_1$Prelude__Basics__No;
        } else {
            return new $HC_1_0$Prelude__Basics__Yes($HC_0_0$Refl);
        }
    }
}

// Decidable.Equality.Decidable.Equality.Nat implementation of Decidable.Equality.DecEq, method decEq

function Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Nat_58__33_decEq_58_0($_0_arg, $_1_arg){
    
    if($_1_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
        
        if($_0_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
            return new $HC_1_0$Prelude__Basics__Yes($HC_0_0$Refl);
        } else {
            const $_2_in = $_0_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
            return $HC_0_1$Prelude__Basics__No;
        }
    } else {
        const $_3_in = $_1_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
        
        if($_0_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
            return $HC_0_1$Prelude__Basics__No;
        } else {
            const $_4_in = $_0_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
            const $cg$5 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Nat_58__33_decEq_58_0($_4_in, $_3_in);
            if(($cg$5.type === 1)) {
                return $HC_0_1$Prelude__Basics__No;
            } else {
                return new $HC_1_0$Prelude__Basics__Yes($HC_0_0$Refl);
            }
        }
    }
}

// Prelude.Interfaces.Data.Fin.Fin n implementation of Prelude.Interfaces.Eq, method ==

function Prelude__Interfaces__Data__Fin___64_Prelude__Interfaces__Eq_36_Fin_32_n_58__33__61__61__58_0($_0_arg, $_1_arg, $_2_arg){
    for(;;) {
        
        if(($_2_arg.type === 1)) {
            
            if(($_1_arg.type === 1)) {
                
                if($_0_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
                    return false;
                } else {
                    const $_5_in = $_0_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
                    $_0_arg = $_5_in;
                    $_1_arg = $_1_arg.$1;
                    $_2_arg = $_2_arg.$1;
                }
            } else {
                return false;
            }
        } else if(($_2_arg.type === 0)) {
            
            if(($_1_arg.type === 0)) {
                
                if($_0_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
                    return false;
                } else {
                    const $_6_in = $_0_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
                    return true;
                }
            } else {
                return false;
            }
        } else {
            return false;
        }
    }
}

// Prelude.Interfaces.Prelude.Nat.Nat implementation of Prelude.Interfaces.Eq, method ==

function Prelude__Interfaces__Prelude__Nat___64_Prelude__Interfaces__Eq_36_Nat_58__33__61__61__58_0($_0_arg, $_1_arg){
    for(;;) {
        
        if($_1_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
            
            if($_0_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
                return true;
            } else {
                return false;
            }
        } else {
            const $_2_in = $_1_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
            
            if($_0_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
                return false;
            } else {
                const $_3_in = $_0_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
                $_0_arg = $_3_in;
                $_1_arg = $_2_in;
            }
        }
    }
}

// Prelude.Foldable.Prelude.List.List implementation of Prelude.Foldable.Foldable, method foldl

function Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldl_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    let $tco$$_3_arg = $_3_arg;
    for(;;) {
        
        if(($_4_arg.type === 1)) {
            $tco$$_3_arg = $_2_arg($_3_arg)($_4_arg.$1);
            $_0_arg = null;
            $_1_arg = null;
            $_2_arg = $_2_arg;
            $_3_arg = $tco$$_3_arg;
            $_4_arg = $_4_arg.$2;
        } else {
            return $_3_arg;
        }
    }
}

// Prelude.Foldable.Prelude.List.List implementation of Prelude.Foldable.Foldable, method foldr

function Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    
    if(($_4_arg.type === 1)) {
        return $_2_arg($_4_arg.$1)(Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $_2_arg, $_3_arg, $_4_arg.$2));
    } else {
        return $_3_arg;
    }
}

// Prelude.Foldable.Prelude.Maybe.Maybe implementation of Prelude.Foldable.Foldable, method foldr

function Prelude__Foldable__Prelude__Maybe___64_Prelude__Foldable__Foldable_36_Maybe_58__33_foldr_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    
    if(($_4_arg.type === 1)) {
        return $_2_arg($_4_arg.$1)($_3_arg);
    } else {
        return $_3_arg;
    }
}

// Prelude.Functor.Prelude.List.List implementation of Prelude.Functor.Functor, method map

function Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    if(($_3_arg.type === 1)) {
        return new $HC_2_1$Prelude__List___58__58_($_2_arg($_3_arg.$1), Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $_2_arg, $_3_arg.$2));
    } else {
        return $_3_arg;
    }
}

// Prelude.Functor.Prelude.Maybe implementation of Prelude.Functor.Functor, method map

function Prelude__Functor__Prelude___64_Prelude__Functor__Functor_36_Maybe_58__33_map_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    if(($_3_arg.type === 1)) {
        return new $HC_1_1$Prelude__Maybe__Just($_2_arg($_3_arg.$1));
    } else {
        return $_3_arg;
    }
}

// Prelude.Functor.TParsec.Result.Result e implementation of Prelude.Functor.Functor, method map

function Prelude__Functor__TParsec__Result___64_Prelude__Functor__Functor_36_Result_32_e_58__33_map_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    
    if(($_4_arg.type === 0)) {
        return $_4_arg;
    } else if(($_4_arg.type === 1)) {
        return $_4_arg;
    } else {
        return new $HC_1_2$TParsec__Result__Value($_3_arg($_4_arg.$1));
    }
}

// Prelude.Functor.TParsec.Result.ResultT e m implementation of Prelude.Functor.Functor, method map

function Prelude__Functor__TParsec__Result___64_Prelude__Functor__Functor_36_ResultT_32_e_32_m_58__33_map_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg){
    return $_4_arg(null)(null)($partial_1_2$Prelude__Functor___123_TParsec__Result___64_Prelude__Functor__Functor_36_ResultT_32_e_32_m_58__33_map_58_0_95_lam_95_5281_125_($_5_arg))($_6_arg);
}

// Prelude.Functor.Control.Monad.State.StateT stateType f implementation of Prelude.Functor.Functor, method map

function Prelude__Functor__Control__Monad__State___64_Prelude__Functor__Functor_36_StateT_32_stateType_32_f_58__33_map_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_st){
    return $_4_arg(null)(null)($partial_1_2$Prelude__Functor___123_Control__Monad__State___64_Prelude__Functor__Functor_36_StateT_32_stateType_32_f_58__33_map_58_0_95_lam_95_5282_125_($_5_arg))($_6_arg($_7_st));
}

// Prelude.Functor.TParsec.Types.TParsecT e a m implementation of Prelude.Functor.Functor, method map

function Prelude__Functor__TParsec__Types___64_Prelude__Functor__Functor_36_TParsecT_32_e_32_a_32_m_58__33_map_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    return $partial_7_8$Prelude__Functor__Control__Monad__State___64_Prelude__Functor__Functor_36_StateT_32_stateType_32_f_58__33_map_58_0(null, null, null, null, $partial_1_5$Prelude__Functor___123_TParsec__Types___64_Prelude__Functor__Functor_36_TParsecT_32_e_32_a_32_m_58__33_map_58_0_95_lam_95_5283_125_($_5_arg), $_6_arg, $_7_arg);
}

// Prelude.Functor.Data.Vect.Vect n implementation of Prelude.Functor.Functor, method map

function Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    
    if(($_4_arg.type === 1)) {
        return new $HC_2_1$Data__Vect___58__58_($_3_arg($_4_arg.$1), Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $_3_arg, $_4_arg.$2));
    } else {
        return $_4_arg;
    }
}

// Prelude.Monad.TParsec.Result.ResultT e m implementation of Prelude.Monad.Monad, method >>=

function Prelude__Monad__TParsec__Result___64_Prelude__Monad__Monad_36_ResultT_32_e_32_m_58__33__62__62__61__58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg){
    
    return $_4_arg.$2(null)(null)($_5_arg)($partial_2_3$Prelude__Monad___123_TParsec__Result___64_Prelude__Monad__Monad_36_ResultT_32_e_32_m_58__33__62__62__61__58_0_95_lam_95_5284_125_($_4_arg, $_6_arg));
}

// Prelude.Monad.Control.Monad.State.StateT stateType m implementation of Prelude.Monad.Monad, method >>=

function Prelude__Monad__Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_st){
    
    return $_4_arg.$2(null)(null)($_5_arg($_7_st))($partial_1_2$Prelude__Monad___123_Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0_95_lam_95_5285_125_($_6_arg));
}

// Prelude.Monad.TParsec.Types.TParsecT e a m implementation of Prelude.Monad.Monad, method >>=

function Prelude__Monad__TParsec__Types___64_Prelude__Monad__Monad_36_TParsecT_32_e_32_a_32_m_58__33__62__62__61__58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    return $partial_7_8$Prelude__Monad__Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_1_5$Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5277_125_($_5_arg), $partial_1_3$Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5278_125_($_5_arg), $partial_1_5$Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5279_125_($_5_arg)), $partial_1_5$Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5280_125_($_5_arg)), $_6_arg, $_7_arg);
}

// TParsec.Running.TParsec.Running.ResultT e m implementation of TParsec.Running.MonadRun, method runMonad

function TParsec__Running__TParsec__Running___64_TParsec__Running__MonadRun_36_ResultT_32_e_32_m_58__33_runMonad_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    return Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $partial_0_2$TParsec__Running___123_TParsec__Running___64_TParsec__Running__MonadRun_36_ResultT_32_e_32_m_58__33_runMonad_58_0_95_lam_95_5290_125_(), $HC_0_0$Prelude__List__Nil, $_3_arg(null)($_4_arg));
}

// TParsec.Running.Parse.StateT PState Identity implementation of TParsec.Running.MonadRun, method runMonad

function TParsec__Running__Parse___64_TParsec__Running__MonadRun_36_StateT_32_PState_32_Identity_58__33_runMonad_58_0($_0_arg, $_1_arg){
    return new $HC_2_1$Prelude__List___58__58_(Control__Monad__State__evalState(null, null, $_1_arg, new $HC_1_0$Data__SortedMap__Empty(new $HC_3_0$Prelude__Interfaces__Ord_95_ictor(new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Backend__JSON___123_makeDefs_95_161_125_(), $partial_0_2$Backend__JSON___123_makeDefs_95_162_125_()), $partial_0_2$TParsec__Running___123_Parse___64_TParsec__Running__MonadRun_36_StateT_32_PState_32_Identity_58__33_runMonad_58_0_95_lam_95_5293_125_(), $partial_0_2$TParsec__Running___123_Parse___64_TParsec__Running__MonadRun_36_StateT_32_PState_32_Identity_58__33_runMonad_58_0_95_lam_95_5294_125_()))), $HC_0_0$Prelude__List__Nil);
}

// TParsec.Running.TParsec.Running.TParsecT e a m implementation of TParsec.Running.MonadRun, method runMonad

function TParsec__Running__TParsec__Running___64_TParsec__Running__MonadRun_36_TParsecT_32_e_32_a_32_m_58__33_runMonad_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg){
    return Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $partial_0_1$TParsec__Running___123_TParsec__Running___64_TParsec__Running__MonadRun_36_TParsecT_32_e_32_a_32_m_58__33_runMonad_58_0_95_lam_95_5295_125_(), TParsec__Running__TParsec__Running___64_TParsec__Running__MonadRun_36_ResultT_32_e_32_m_58__33_runMonad_58_0(null, null, null, $_4_arg, $_5_arg(new $HC_2_0$Builtins__MkPair($HC_0_0$TParsec__Types__MkPosition, $HC_0_0$Prelude__List__Nil))));
}

// Control.Monad.Trans.TParsec.Result.ResultT e implementation of Control.Monad.Trans.MonadTrans, method lift

function Control__Monad__Trans__TParsec__Result___64_Control__Monad__Trans__MonadTrans_36_ResultT_32_e_58__33_lift_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_18_in){
    
    const $cg$3 = $_3_arg.$1;
    return $cg$3.$1(null)(null)($partial_0_1$Control__Monad__Trans___123_TParsec__Result___64_Control__Monad__Trans__MonadTrans_36_ResultT_32_e_58__33_lift_58_0_95_lam_95_5296_125_())($_18_in);
}

// Control.Monad.Trans.Control.Monad.State.StateT stateType implementation of Control.Monad.Trans.MonadTrans, method lift

function Control__Monad__Trans__Control__Monad__State___64_Control__Monad__Trans__MonadTrans_36_StateT_32_stateType_58__33_lift_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_st){
    
    return $_3_arg.$2(null)(null)($_4_arg)($partial_2_3$Control__Monad__Trans___123_Control__Monad__State___64_Control__Monad__Trans__MonadTrans_36_StateT_32_stateType_58__33_lift_58_0_95_lam_95_5297_125_($_3_arg, $_5_st));
}

// Control.Monad.Trans.TParsec.Types.TParsecT e a implementation of Control.Monad.Trans.MonadTrans, method lift

function Control__Monad__Trans__TParsec__Types___64_Control__Monad__Trans__MonadTrans_36_TParsecT_32_e_32_a_58__33_lift_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_61_in){
    return $partial_5_6$Control__Monad__Trans__Control__Monad__State___64_Control__Monad__Trans__MonadTrans_36_StateT_32_stateType_58__33_lift_58_0(null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_1_5$Control__Monad__Trans___123_TParsec__Types___64_Control__Monad__Trans__MonadTrans_36_TParsecT_32_e_32_a_58__33_lift_58_0_95_lam_95_5298_125_($_4_arg), $partial_1_3$Control__Monad__Trans___123_TParsec__Types___64_Control__Monad__Trans__MonadTrans_36_TParsecT_32_e_32_a_58__33_lift_58_0_95_lam_95_5299_125_($_4_arg), $partial_1_5$Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5279_125_($_4_arg)), $partial_1_5$Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5280_125_($_4_arg)), Control__Monad__Trans__TParsec__Result___64_Control__Monad__Trans__MonadTrans_36_ResultT_32_e_58__33_lift_58_0(null, null, null, $_4_arg, $_61_in));
}

// Prelude.Interfaces.Prelude.Interfaces.Char implementation of Prelude.Interfaces.Ord, method compare

function Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Char_58__33_compare_58_0($_0_arg, $_1_arg){
    
    if((((($_0_arg === $_1_arg)) ? 1|0 : 0|0) === 0)) {
        
        if((((($_0_arg < $_1_arg)) ? 1|0 : 0|0) === 0)) {
            return 1;
        } else {
            return -1;
        }
    } else {
        return 0;
    }
}

// Prelude.Interfaces.Prelude.Interfaces.Int implementation of Prelude.Interfaces.Ord, method compare

function Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Int_58__33_compare_58_0($_0_arg, $_1_arg){
    
    if((((($_0_arg === $_1_arg)) ? 1|0 : 0|0) === 0)) {
        
        if((((($_0_arg < $_1_arg)) ? 1|0 : 0|0) === 0)) {
            return 1;
        } else {
            return -1;
        }
    } else {
        return 0;
    }
}

// Prelude.Interfaces.Prelude.Interfaces.Integer implementation of Prelude.Interfaces.Ord, method compare

function Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Integer_58__33_compare_58_0($_0_arg, $_1_arg){
    
    if(((($_0_arg.equals($_1_arg)) ? 1|0 : 0|0) === 0)) {
        
        if(((((($_0_arg).compareTo(($_1_arg)) < 0)) ? 1|0 : 0|0) === 0)) {
            return 1;
        } else {
            return -1;
        }
    } else {
        return 0;
    }
}

// Prelude.Interfaces.Prelude.Interfaces.String implementation of Prelude.Interfaces.Ord, method compare

function Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_String_58__33_compare_58_0($_0_arg, $_1_arg){
    
    if((((($_0_arg == $_1_arg)) ? 1|0 : 0|0) === 0)) {
        
        if((((($_0_arg < $_1_arg)) ? 1|0 : 0|0) === 0)) {
            return 1;
        } else {
            return -1;
        }
    } else {
        return 0;
    }
}

// Prelude.Traversable.Prelude.List implementation of Prelude.Traversable.Traversable, method traverse

function Prelude__Traversable__Prelude___64_Prelude__Traversable__Traversable_36_List_58__33_traverse_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg){
    
    if(($_5_arg.type === 1)) {
        
        let $cg$4 = null;
        let $cg$5 = null;
        $cg$5 = $_3_arg.$2(null)($partial_0_2$Backend__JSON___123_disjointSubSchema_95_29_125_());
        $cg$4 = $_3_arg.$3(null)(null)($cg$5)($_4_arg($_5_arg.$1));
        return $_3_arg.$3(null)(null)($cg$4)(Prelude__Traversable__Prelude___64_Prelude__Traversable__Traversable_36_List_58__33_traverse_58_0(null, null, null, $_3_arg, $_4_arg, $_5_arg.$2));
    } else {
        
        return $_3_arg.$2(null)($HC_0_0$Prelude__List__Nil);
    }
}

// Prelude.Traversable.Data.Vect.Vect n implementation of Prelude.Traversable.Traversable, method traverse

function Prelude__Traversable__Data__Vect___64_Prelude__Traversable__Traversable_36_Vect_32_n_58__33_traverse_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg){
    
    if(($_6_arg.type === 1)) {
        
        let $cg$4 = null;
        let $cg$5 = null;
        $cg$5 = $_4_arg.$2(null)($partial_0_2$Prelude__Traversable___123_Data__Vect___64_Prelude__Traversable__Traversable_36_Vect_32_n_58__33_traverse_58_0_95_lam_95_5303_125_());
        $cg$4 = $_4_arg.$3(null)(null)($cg$5)($_5_arg($_6_arg.$1));
        return $_4_arg.$3(null)(null)($cg$4)(Prelude__Traversable__Data__Vect___64_Prelude__Traversable__Traversable_36_Vect_32_n_58__33_traverse_58_0(null, null, null, null, $_4_arg, $_5_arg, $_6_arg.$2));
    } else {
        
        return $_4_arg.$2(null)($HC_0_0$Data__Vect__Nil);
    }
}

// {Induction.Nat.fixBox:go:0_lam_4513}

function $_4513_Induction__Nat__fixBox_58_go_58_0_95_lam($_0_lift){
    return null;
}

// {Induction.Nat.fixBox:go:0_lam_4514}

function $_4514_Induction__Nat__fixBox_58_go_58_0_95_lam($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return Induction__Nat__fixBox_58_go_58_0(null, $_0_lift, null, $_1_lift, $_2_lift)(Prelude__Nat__lteTransitive(null, null, null, $_3_lift, null));
}

// {Induction.Nat.fixBox:go:0_lam_4515}

function $_4515_Induction__Nat__fixBox_58_go_58_0_95_lam($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return $_0_lift($_1_lift)($partial_2_4$$_4514_Induction__Nat__fixBox_58_go_58_0_95_lam($_0_lift, $_2_lift));
}

// {Backend.Utils.flattenMus:flattenMu:0_lam_4516}

function $_4516_Backend__Utils__flattenMus_58_flattenMu_58_0_95_lam($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    
    return new $HC_2_0$Builtins__MkPair($_3_lift.$1, Backend__Utils__flattenMus_58_flattenMu_58_0($_0_lift.add((new $JSRTS.jsbn.BigInteger(("1")))), null, new $HC_2_1$Data__Vect___58__58_(Backend__Utils__nameMu(null, null, $_1_lift), $_2_lift), $_3_lift.$2));
}

// {Text.PrettyPrint.WL.Core.render:best:0_lam_4517}

function $_4517_Text__PrettyPrint__WL__Core__render_58_best_58_0_95_lam($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift){
    return Text__PrettyPrint__WL__Core__render_58_best_58_0($_0_lift, $_1_lift, null, $_2_lift, $_6_lift, $_3_lift, $_4_lift, $_5_lift);
}

// {Text.PrettyPrint.WL.Core.render:best:0_lam_4518}

function $_4518_Text__PrettyPrint__WL__Core__render_58_best_58_0_95_lam($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift){
    return Text__PrettyPrint__WL__Core__render_58_best_58_0($_0_lift, $_1_lift, null, $_2_lift, $_3_lift, $_4_lift, $JSRTS.force($_5_lift), $_6_lift);
}

// {Parse.tdef:nary:0_lam_4522}

function $_4522_Parse__tdef_58_nary_58_0_95_lam($_0_lift, $_1_lift){
    
    const $cg$3 = $_1_lift.$2;
    return Typedefs__weakenTDef(null, $cg$3.$2, $_0_lift, $cg$3.$1);
}

// {Parse.tdef:nary:0_lam_4523}

function $_4523_Parse__tdef_58_nary_58_0_95_lam($_0_lift, $_1_lift){
    
    const $cg$3 = $_1_lift.$2;
    let $cg$2 = null;
    $cg$2 = new $HC_2_1$Data__Vect___58__58_($cg$3.$1, Data__Vect__fromList(null, $cg$3.$2));
    const $cg$5 = Parse__toVMax(null, null, new $HC_2_1$Data__Vect___58__58_($_1_lift.$1, $cg$2));
    const $cg$7 = $_1_lift.$2;
    let $cg$6 = null;
    $cg$6 = $cg$7.$2;
    return new $HC_2_0$Builtins__MkDPair($cg$5.$1, $_0_lift(Prelude__List__length(null, $cg$6))($cg$5.$1)(Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_1_2$$_4522_Parse__tdef_58_nary_58_0_95_lam($cg$5.$1), Parse__fromVMax_58_go_58_0(null, $cg$5.$1, null, null, null, null, Prelude__Nat__lteRefl($cg$5.$1), $cg$5.$2))));
}

// {Parse.tdef:nary:0_lam_5269}

function $_5269_Parse__tdef_58_nary_58_0_95_lam($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift, $_7_lift){
    return TParsec__Combinators__nelist(null, null, null, new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $_0_lift)(Parse__ignorespaces(null, null, $partial_0_3$Parse___123_tdef_95_431_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $partial_0_1$Typedefs___123_apN_95_20_125_(), new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Parse___123_tdef_95_538_125_(), $partial_0_2$Parse___123_tdef_95_539_125_()), $partial_0_2$Parse___123_tdef_95_540_125_(), $_0_lift, $_1_lift($_0_lift)($_2_lift)))($_6_lift)(Prelude__Nat__lteTransitive(null, null, null, $_7_lift, null));
}

// {Parse.tdef:nary:0_lam_5270}

function $_5270_Parse__tdef_58_nary_58_0_95_lam($_0_lift, $_1_lift, $_2_lift){
    return $partial_8_11$TParsec__Combinators__andbind(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), null, Parse__ignorespaces(null, null, $partial_0_3$Parse___123_tdef_95_431_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $partial_0_1$Typedefs___123_apN_95_20_125_(), new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Parse___123_tdef_95_538_125_(), $partial_0_2$Parse___123_tdef_95_539_125_()), $partial_0_2$Parse___123_tdef_95_540_125_(), $_1_lift, $_0_lift($_1_lift)($_2_lift)), $partial_3_8$$_5269_Parse__tdef_58_nary_58_0_95_lam($_1_lift, $_0_lift, $_2_lift));
}

// {Parse.tdef:nary:0_lam_5271}

function $_5271_Parse__tdef_58_nary_58_0_95_lam($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift){
    return TParsec__Combinators__rand(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), null, null, Parse__ignorespaces(null, null, $partial_0_3$Parse___123_tdef_95_431_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $partial_0_1$Typedefs___123_apN_95_20_125_(), new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Parse___123_tdef_95_538_125_(), $partial_0_2$Parse___123_tdef_95_539_125_()), $partial_0_2$Parse___123_tdef_95_540_125_(), $_0_lift, TParsec__Combinators__Chars__char(null, $partial_0_3$Parse___123_tdef_95_431_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $partial_0_1$Typedefs___123_apN_95_20_125_(), new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Parse___123_tdef_95_538_125_(), $partial_0_2$Parse___123_tdef_95_539_125_()), $partial_0_2$Parse___123_tdef_95_540_125_(), $_1_lift)($_0_lift)), $partial_1_3$$_5270_Parse__tdef_58_nary_58_0_95_lam($_2_lift))($_5_lift)(Prelude__Nat__lteTransitive(null, null, null, $_6_lift, null));
}

// Prelude.Bits.b8ToHexString, getDigit

function Prelude__Bits__b8ToHexString_58_getDigit_58_0($_0_arg, $_1_arg){
    const $_2_in = $_1_arg;
    let $cg$1 = null;
    if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Int_58__33_compare_58_0($_2_in, 0) > 0)) {
        $cg$1 = true;
    } else {
        $cg$1 = ($_2_in === 0);
    }
    
    let $cg$2 = null;
    if($cg$1) {
        
        if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Int_58__33_compare_58_0($_2_in, 9) < 0)) {
            $cg$2 = true;
        } else {
            $cg$2 = ($_2_in === 9);
        }
    } else {
        $cg$2 = false;
    }
    
    
    if($cg$2) {
        return (String.fromCharCode(("0").charCodeAt(0) + (Prelude__Chars__chr($_2_in)).charCodeAt(0)));
    } else {
        let $cg$5 = null;
        if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Int_58__33_compare_58_0($_2_in, 10) > 0)) {
            $cg$5 = true;
        } else {
            $cg$5 = ($_2_in === 10);
        }
        
        let $cg$6 = null;
        if($cg$5) {
            
            if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Int_58__33_compare_58_0($_2_in, 15) < 0)) {
                $cg$6 = true;
            } else {
                $cg$6 = ($_2_in === 15);
            }
        } else {
            $cg$6 = false;
        }
        
        
        if($cg$6) {
            return (String.fromCharCode(("A").charCodeAt(0) + (Prelude__Chars__chr(($_2_in - 10))).charCodeAt(0)));
        } else {
            return "?";
        }
    }
}

// Backend.JSON.disjointSubSchema, makeCase

function Backend__JSON__disjointSubSchema_58_makeCase_58_0($_0_arg, $_1_arg, $_2_arg){
    
    return new $HC_1_5$Language__JSON__Data__JObject(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("type", new $HC_1_3$Language__JSON__Data__JString("object")), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("required", new $HC_1_4$Language__JSON__Data__JArray(new $HC_2_1$Prelude__List___58__58_(new $HC_1_3$Language__JSON__Data__JString($_2_arg.$1), $HC_0_0$Prelude__List__Nil))), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("additionalProperties", new $HC_1_1$Language__JSON__Data__JBoolean(false)), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("properties", new $HC_1_5$Language__JSON__Data__JObject(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair($_2_arg.$1, Backend__JSON__makeSubSchema($_2_arg.$2)), $HC_0_0$Prelude__List__Nil))), $HC_0_0$Prelude__List__Nil)))));
}

// Induction.Nat.fixBox, go

function Induction__Nat__fixBox_58_go_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_in){
    
    if($_3_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
        return $partial_0_1$$_4513_Induction__Nat__fixBox_58_go_58_0_95_lam();
    } else {
        const $_6_in = $_3_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
        return $partial_3_4$$_4515_Induction__Nat__fixBox_58_go_58_0_95_lam($_1_arg, $_4_in, $_6_in);
    }
}

// Backend.Utils.flattenMus, flattenMu

function Backend__Utils__flattenMus_58_flattenMu_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    if(($_3_arg.type === 0)) {
        return $_3_arg;
    } else if(($_3_arg.type === 1)) {
        return $_3_arg;
    } else if(($_3_arg.type === 6)) {
        return new $HC_3_6$Typedefs__TApp($_3_arg.$1, $_3_arg.$2, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_3_4$Backend__Utils__flattenMus_58_flattenMu_58_0($_0_arg, null, $_2_arg), $_3_arg.$3));
    } else if(($_3_arg.type === 5)) {
        return new $HC_2_5$Typedefs__TMu($_3_arg.$1, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_3_4$$_4516_Backend__Utils__flattenMus_58_flattenMu_58_0_95_lam($_0_arg, $_3_arg.$2, $_2_arg), $_3_arg.$2));
    } else if(($_3_arg.type === 3)) {
        return new $HC_2_3$Typedefs__TProd($_3_arg.$1, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_3_4$Backend__Utils__flattenMus_58_flattenMu_58_0($_0_arg, null, $_2_arg), $_3_arg.$2));
    } else if(($_3_arg.type === 2)) {
        return new $HC_2_2$Typedefs__TSum($_3_arg.$1, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_3_4$Backend__Utils__flattenMus_58_flattenMu_58_0($_0_arg, null, $_2_arg), $_3_arg.$2));
    } else {
        return new $HC_3_6$Typedefs__TApp($_0_arg, new $HC_2_0$Typedefs__TName(Data__Vect__index(null, null, $_3_arg.$1, $_2_arg), $HC_0_0$Typedefs__T0), Typedefs__idVars($_0_arg));
    }
}

// Data.NEList.foldr1, go

function Data__NEList__foldr1_58_go_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg){
    
    if(($_5_arg.type === 1)) {
        return $_1_arg($_4_arg)(Data__NEList__foldr1_58_go_58_0(null, $_1_arg, null, null, $_5_arg.$1, $_5_arg.$2));
    } else {
        return $_4_arg;
    }
}

// Language.JSON.Data.format, formatValue

function Language__JSON__Data__format_58_formatValue_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg){
    
    if(($_5_arg.type === 4)) {
        const $cg$5 = $_5_arg.$1;
        if(($cg$5.type === 1)) {
            return ("[\n" + (Language__JSON__Data__format_58_formatValue_58_0_58_formatValues_58_1(null, null, null, $_3_arg, $_4_arg, null, null, new $HC_2_1$Prelude__List___58__58_($cg$5.$1, $cg$5.$2), null) + (Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $partial_0_2$prim_95__95_strCons(), "", Prelude__List__replicate(null, $_3_arg, " ")) + "]")));
        } else if(($cg$5.type === 0)) {
            return "[]";
        } else {
            return Language__JSON__Data__stringify($_5_arg);
        }
    } else if(($_5_arg.type === 5)) {
        const $cg$3 = $_5_arg.$1;
        if(($cg$3.type === 1)) {
            return ("{\n" + (Language__JSON__Data__format_58_formatValue_58_0_58_formatProps_58_3(null, null, null, $_3_arg, $_4_arg, null, null, new $HC_2_1$Prelude__List___58__58_($cg$3.$1, $cg$3.$2), null) + (Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $partial_0_2$prim_95__95_strCons(), "", Prelude__List__replicate(null, $_3_arg, " ")) + "}")));
        } else if(($cg$3.type === 0)) {
            return "{}";
        } else {
            return Language__JSON__Data__stringify($_5_arg);
        }
    } else {
        return Language__JSON__Data__stringify($_5_arg);
    }
}

// Parse.fromVMax, go

function Parse__fromVMax_58_go_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    
    if(($_7_arg.type === 1)) {
        return new $HC_2_1$Data__Vect___58__58_(new $HC_2_0$Builtins__MkDPair($_7_arg.$1, new $HC_2_0$Builtins__MkPair(Prelude__Nat__lteTransitive(null, null, null, $_7_arg.$4, null), $_7_arg.$2)), Parse__fromVMax_58_go_58_0(null, $_1_arg, null, null, null, null, $_6_arg, $_7_arg.$3));
    } else if(($_7_arg.type === 2)) {
        return new $HC_2_1$Data__Vect___58__58_(new $HC_2_0$Builtins__MkDPair($_1_arg, new $HC_2_0$Builtins__MkPair($_6_arg, $_7_arg.$2)), Parse__fromVMax_58_go_58_0(null, $_7_arg.$1, null, null, null, null, Prelude__Nat__lteTransitive(null, null, null, $_7_arg.$4, null), $_7_arg.$3));
    } else {
        return new $HC_2_1$Data__Vect___58__58_(new $HC_2_0$Builtins__MkDPair($_1_arg, new $HC_2_0$Builtins__MkPair($_6_arg, $_7_arg.$1)), $HC_0_0$Data__Vect__Nil);
    }
}

// Text.PrettyPrint.WL.Combinators.literal, mkLiteral

function Text__PrettyPrint__WL__Combinators__literal_58_mkLiteral_58_0($_0_arg, $_1_arg){
    
    if(($_1_arg.type === 1)) {
        
        if(($_1_arg.$1 === "\n")) {
            return new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(new $HC_1_3$Text__PrettyPrint__WL__Core__Line(false), Text__PrettyPrint__WL__Combinators__literal_58_mkLiteral_58_0(null, $_1_arg.$2));
        } else {
            return new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__char($_1_arg.$1), Text__PrettyPrint__WL__Combinators__literal_58_mkLiteral_58_0(null, $_1_arg.$2));
        }
    } else {
        return $HC_0_0$Text__PrettyPrint__WL__Core__Empty;
    }
}

// Backend.JSON.makeDefs, emptyType

function Backend__JSON__makeDefs_58_emptyType_58_0(){
    return new $HC_1_5$Language__JSON__Data__JObject(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("type", new $HC_1_3$Language__JSON__Data__JString("array")), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("items", new $HC_1_5$Language__JSON__Data__JObject(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("type", new $HC_1_3$Language__JSON__Data__JString("boolean")), $HC_0_0$Prelude__List__Nil))), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("minItems", new $HC_1_2$Language__JSON__Data__JNumber(3.0)), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("uniqueItems", new $HC_1_1$Language__JSON__Data__JBoolean(true)), $HC_0_0$Prelude__List__Nil)))));
}

// Prelude.List.nubBy, nubBy'

function Prelude__List__nubBy_58_nubBy_39__58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    for(;;) {
        
        if(($_3_arg.type === 1)) {
            
            if(Prelude__List__elemBy(null, $_2_arg, $_3_arg.$1, $_1_arg)) {
                $_0_arg = null;
                $_1_arg = $_1_arg;
                $_2_arg = $_2_arg;
                $_3_arg = $_3_arg.$2;
            } else {
                return new $HC_2_1$Prelude__List___58__58_($_3_arg.$1, Prelude__List__nubBy_58_nubBy_39__58_0(null, new $HC_2_1$Prelude__List___58__58_($_3_arg.$1, $_1_arg), $_2_arg, $_3_arg.$2));
            }
        } else {
            return $_3_arg;
        }
    }
}

// Text.PrettyPrint.WL.Core.render, best

function Text__PrettyPrint__WL__Core__render_58_best_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    let $tco$$_6_arg = $_6_arg;
    let $tco$$_7_arg = $_7_arg;
    for(;;) {
        
        if(($_6_arg.type === 4)) {
            $tco$$_7_arg = $partial_6_7$$_4517_Text__PrettyPrint__WL__Core__render_58_best_58_0_95_lam($_0_arg, $_1_arg, $_3_arg, $_5_arg, $_6_arg.$2, $_7_arg);
            $_0_arg = $_0_arg;
            $_1_arg = $_1_arg;
            $_2_arg = null;
            $_3_arg = $_3_arg;
            $_4_arg = $_4_arg;
            $_5_arg = $_5_arg;
            $_6_arg = $_6_arg.$1;
            $_7_arg = $tco$$_7_arg;
        } else if(($_6_arg.type === 1)) {
            return new $HC_2_1$Text__PrettyPrint__WL__Core__PrettyDoc__Chara($_6_arg.$1, $_7_arg(($_4_arg + 1)));
        } else if(($_6_arg.type === 7)) {
            $tco$$_6_arg = $_6_arg.$1($_4_arg);
            $_0_arg = $_0_arg;
            $_1_arg = $_1_arg;
            $_2_arg = null;
            $_3_arg = $_3_arg;
            $_4_arg = $_4_arg;
            $_5_arg = $_5_arg;
            $_6_arg = $tco$$_6_arg;
            $_7_arg = $_7_arg;
        } else if(($_6_arg.type === 0)) {
            return $_7_arg($_4_arg);
        } else if(($_6_arg.type === 3)) {
            return new $HC_2_3$Text__PrettyPrint__WL__Core__PrettyDoc__Line($_5_arg, $_7_arg($_5_arg));
        } else if(($_6_arg.type === 5)) {
            $_0_arg = $_0_arg;
            $_1_arg = $_1_arg;
            $_2_arg = null;
            $_3_arg = $_3_arg;
            $_4_arg = $_4_arg;
            $_5_arg = ($_5_arg + $_6_arg.$1);
            $_6_arg = $_6_arg.$2;
            $_7_arg = $_7_arg;
        } else if(($_6_arg.type === 8)) {
            $tco$$_6_arg = $_6_arg.$1($_5_arg);
            $_0_arg = $_0_arg;
            $_1_arg = $_1_arg;
            $_2_arg = null;
            $_3_arg = $_3_arg;
            $_4_arg = $_4_arg;
            $_5_arg = $_5_arg;
            $_6_arg = $tco$$_6_arg;
            $_7_arg = $_7_arg;
        } else if(($_6_arg.type === 2)) {
            return new $HC_3_2$Text__PrettyPrint__WL__Core__PrettyDoc__Text($_6_arg.$1, $_6_arg.$2, $_7_arg(($_4_arg + $_6_arg.$1)));
        } else {
            return Text__PrettyPrint__WL__Core__render_58_nicest_58_0($_0_arg, $_1_arg, null, $_3_arg, $_4_arg, Text__PrettyPrint__WL__Core__render_58_best_58_0($_0_arg, $_1_arg, null, $_3_arg, $_4_arg, $_5_arg, $_6_arg.$1, $_7_arg), new $JSRTS.Lazy((function(){
                return (function(){
                    return $_4518_Text__PrettyPrint__WL__Core__render_58_best_58_0_95_lam($_0_arg, $_1_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg.$2, $_7_arg);
                })();
            })));
        }
    }
}

// Text.PrettyPrint.WL.Core.render, nicest

function Text__PrettyPrint__WL__Core__render_58_nicest_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg){
    let $cg$1 = null;
    if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Int_58__33_compare_58_0(($_1_arg - $_4_arg), ((Text__PrettyPrint__WL__Core__render_58_rwidth_58_0($_0_arg, $_1_arg, null) - $_4_arg) + $_3_arg)) < 0)) {
        $cg$1 = ($_1_arg - $_4_arg);
    } else {
        $cg$1 = ((Text__PrettyPrint__WL__Core__render_58_rwidth_58_0($_0_arg, $_1_arg, null) - $_4_arg) + $_3_arg);
    }
    
    
    if(Text__PrettyPrint__WL__Core__fits($cg$1, $_5_arg)) {
        return $_5_arg;
    } else {
        return $JSRTS.force($_6_arg);
    }
}

// Text.PrettyPrint.WL.Core.render, rwidth

function Text__PrettyPrint__WL__Core__render_58_rwidth_58_0($_0_arg, $_1_arg, $_2_arg){
    let $cg$1 = null;
    if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Int_58__33_compare_58_0($_1_arg, ((($_1_arg * $_0_arg))|0)) < 0)) {
        $cg$1 = $_1_arg;
    } else {
        $cg$1 = ((($_1_arg * $_0_arg))|0);
    }
    
    
    if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Int_58__33_compare_58_0(0, $cg$1) > 0)) {
        return 0;
    } else {
        
        if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Int_58__33_compare_58_0($_1_arg, ((($_1_arg * $_0_arg))|0)) < 0)) {
            return $_1_arg;
        } else {
            return ((($_1_arg * $_0_arg))|0);
        }
    }
}

// Data.Vect.reverse, go

function Data__Vect__reverse_58_go_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg){
    for(;;) {
        
        if(($_6_arg.type === 1)) {
            $_0_arg = null;
            $_1_arg = null;
            $_2_arg = null;
            $_3_arg = null;
            $_4_arg = null;
            $_5_arg = new $HC_2_1$Data__Vect___58__58_($_6_arg.$1, $_5_arg);
            $_6_arg = $_6_arg.$2;
        } else {
            return $_5_arg;
        }
    }
}

// Text.PrettyPrint.WL.Core.showPrettyDoc, showPrettyDocS

function Text__PrettyPrint__WL__Core__showPrettyDoc_58_showPrettyDocS_58_0($_0_arg, $_1_arg, $_2_arg){
    
    if(($_1_arg.type === 1)) {
        return (($_1_arg.$1)+(Text__PrettyPrint__WL__Core__showPrettyDoc_58_showPrettyDocS_58_0(null, $_1_arg.$2, $_2_arg)));
    } else if(($_1_arg.type === 0)) {
        return $_2_arg;
    } else if(($_1_arg.type === 3)) {
        return ((("\n")+(Text__PrettyPrint__WL__Core__spaces($_1_arg.$1))) + Text__PrettyPrint__WL__Core__showPrettyDoc_58_showPrettyDocS_58_0(null, $_1_arg.$2, $_2_arg));
    } else {
        return ($_1_arg.$2 + Text__PrettyPrint__WL__Core__showPrettyDoc_58_showPrettyDocS_58_0(null, $_1_arg.$3, $_2_arg));
    }
}

// Parse.tdef, nary

function Parse__tdef_58_nary_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    return $partial_8_11$TParsec__Combinators__map(null, null, null, null, $partial_0_4$Parse___123_tdef_95_434_125_(), $partial_1_2$$_4523_Parse__tdef_58_nary_58_0_95_lam($_4_arg), null, TParsec__Combinators__Chars__parens(null, null, $partial_0_3$Parse___123_tdef_95_431_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_1$Parse___123_tdef_95_477_125_(), $partial_0_3$Parse___123_tdef_95_491_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_434_125_(), $partial_0_2$Parse___123_tdef_95_448_125_(), $partial_0_4$Parse___123_tdef_95_462_125_()), $partial_0_4$Parse___123_tdef_95_536_125_()), $partial_0_1$Typedefs___123_apN_95_20_125_(), new $HC_2_0$Prelude__Interfaces__Eq_95_ictor($partial_0_2$Parse___123_tdef_95_538_125_(), $partial_0_2$Parse___123_tdef_95_539_125_()), $partial_0_2$Parse___123_tdef_95_540_125_(), $_1_arg, $partial_3_7$$_5271_Parse__tdef_58_nary_58_0_95_lam($_1_arg, $_3_arg, $_2_arg)));
}

// Data.Inspect.Data.Inspect.SizedList a, a implementation of Data.Inspect.Inspect, method inspect, go

function Data__Inspect__Data__Inspect___64_Data__Inspect__Inspect_36_SizedList_32_a_58_a_58__33_inspect_58_0_58_go_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg){
    
    if($_4_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
        return $HC_0_0$Prelude__Maybe__Nothing;
    } else {
        
        return new $HC_1_1$Prelude__Maybe__Just(new $HC_2_0$Builtins__MkPair($_5_arg.$1, $_5_arg.$2));
    }
}

// Data.Vect.intersperse, intersperse'

function Data__Vect__intersperse_58_intersperse_39__58_1($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    
    if(($_7_arg.type === 1)) {
        return new $HC_2_1$Data__Vect___58__58_($_6_arg, new $HC_2_1$Data__Vect___58__58_($_7_arg.$1, Data__Vect__intersperse_58_intersperse_39__58_1(null, null, null, null, null, null, $_6_arg, $_7_arg.$2)));
    } else {
        return $_7_arg;
    }
}

// Backend.JSON.makeDefs, singletonType

function Backend__JSON__makeDefs_58_singletonType_58_1(){
    return new $HC_1_5$Language__JSON__Data__JObject(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("enum", new $HC_1_4$Language__JSON__Data__JArray(new $HC_2_1$Prelude__List___58__58_(new $HC_1_3$Language__JSON__Data__JString("singleton"), $HC_0_0$Prelude__List__Nil))), $HC_0_0$Prelude__List__Nil));
}

// Backend.Haskell.renderDef, renderConstructor

function Backend__Haskell__renderDef_58_renderConstructor_58_1($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    const $cg$3 = $_3_arg.$2;
    if(($cg$3.type === 2)) {
        return Backend__Haskell__renderApp(null, $_3_arg.$1, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Backend__Haskell__guardParen(), $cg$3.$1));
    } else if(($cg$3.type === 1)) {
        return Backend__Haskell__renderApp(null, $_3_arg.$1, $HC_0_0$Data__Vect__Nil);
    } else {
        return Backend__Haskell__renderApp(null, $_3_arg.$1, new $HC_2_1$Data__Vect___58__58_(Backend__Haskell__guardParen($_3_arg.$2), $HC_0_0$Data__Vect__Nil));
    }
}

// Backend.ReasonML.renderDef, renderConstructor

function Backend__ReasonML__renderDef_58_renderConstructor_58_1($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    const $cg$3 = $_3_arg.$2;
    if(($cg$3.type === 1)) {
        let $cg$12 = null;
        if((((($_3_arg.$1 == "")) ? 1|0 : 0|0) === 0)) {
            $cg$12 = true;
        } else {
            $cg$12 = false;
        }
        
        const $cg$14 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$12, true);
        let $cg$13 = null;
        if(($cg$14.type === 1)) {
            $cg$13 = "";
        } else {
            let $cg$15 = null;
            if(Prelude__Chars__isLower($_3_arg.$1[0])) {
                $cg$15 = String.fromCharCode(((($_3_arg.$1[0]).charCodeAt(0)|0) - 32));
            } else {
                $cg$15 = $_3_arg.$1[0];
            }
            
            $cg$13 = (($cg$15)+($_3_arg.$1.slice(1)));
        }
        
        return Backend__ReasonML__renderApp((new $JSRTS.jsbn.BigInteger(("2"))).add($cg$3.$1), $cg$13, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Backend__ReasonML__renderType(), $cg$3.$2));
    } else if(($cg$3.type === 0)) {
        let $cg$8 = null;
        if((((($_3_arg.$1 == "")) ? 1|0 : 0|0) === 0)) {
            $cg$8 = true;
        } else {
            $cg$8 = false;
        }
        
        const $cg$10 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$8, true);
        let $cg$9 = null;
        if(($cg$10.type === 1)) {
            $cg$9 = "";
        } else {
            let $cg$11 = null;
            if(Prelude__Chars__isLower($_3_arg.$1[0])) {
                $cg$11 = String.fromCharCode(((($_3_arg.$1[0]).charCodeAt(0)|0) - 32));
            } else {
                $cg$11 = $_3_arg.$1[0];
            }
            
            $cg$9 = (($cg$11)+($_3_arg.$1.slice(1)));
        }
        
        return Backend__ReasonML__renderApp((new $JSRTS.jsbn.BigInteger(("0"))), $cg$9, $HC_0_0$Data__Vect__Nil);
    } else {
        let $cg$4 = null;
        if((((($_3_arg.$1 == "")) ? 1|0 : 0|0) === 0)) {
            $cg$4 = true;
        } else {
            $cg$4 = false;
        }
        
        const $cg$6 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$4, true);
        let $cg$5 = null;
        if(($cg$6.type === 1)) {
            $cg$5 = "";
        } else {
            let $cg$7 = null;
            if(Prelude__Chars__isLower($_3_arg.$1[0])) {
                $cg$7 = String.fromCharCode(((($_3_arg.$1[0]).charCodeAt(0)|0) - 32));
            } else {
                $cg$7 = $_3_arg.$1[0];
            }
            
            $cg$5 = (($cg$7)+($_3_arg.$1.slice(1)));
        }
        
        return Backend__ReasonML__renderApp((new $JSRTS.jsbn.BigInteger(("1"))), $cg$5, new $HC_2_1$Data__Vect___58__58_(Backend__ReasonML__renderType($_3_arg.$2), $HC_0_0$Data__Vect__Nil));
    }
}

// Language.JSON.Data.format, formatValue, formatValues

function Language__JSON__Data__format_58_formatValue_58_0_58_formatValues_58_1($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_arg){
    
    const $cg$3 = Prelude__List__nonEmpty(null, $_7_arg.$2);
    let $cg$2 = null;
    if(($cg$3.type === 1)) {
        $cg$2 = "\n";
    } else {
        $cg$2 = (",\n" + Language__JSON__Data__format_58_formatValue_58_0_58_formatValues_58_1(null, null, null, $_3_arg, $_4_arg, null, null, $_7_arg.$2, null));
    }
    
    return ((Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $partial_0_2$prim_95__95_strCons(), "", Prelude__List__replicate(null, $_3_arg.add($_4_arg), " ")) + Language__JSON__Data__format_58_formatValue_58_0(null, null, null, $_3_arg.add($_4_arg), $_4_arg, $_7_arg.$1)) + $cg$2);
}

// Backend.ReasonML.makeDefs, eitherDef

function Backend__ReasonML__makeDefs_58_eitherDef_58_3($_0_arg, $_1_arg, $_2_arg){
    const $cg$2 = Data__Fin__integerToFin((new $JSRTS.jsbn.BigInteger(("1"))), (new $JSRTS.jsbn.BigInteger(("3"))));
    let $cg$1 = null;
    $cg$1 = $cg$2.$1;
    const $cg$4 = Data__Fin__integerToFin((new $JSRTS.jsbn.BigInteger(("2"))), (new $JSRTS.jsbn.BigInteger(("3"))));
    let $cg$3 = null;
    $cg$3 = $cg$4.$1;
    return new $HC_2_0$Typedefs__TName("either", new $HC_2_5$Typedefs__TMu((new $JSRTS.jsbn.BigInteger(("2"))), new $HC_2_1$Data__Vect___58__58_(new $HC_2_0$Builtins__MkPair("Left", new $HC_1_4$Typedefs__TVar($cg$1)), new $HC_2_1$Data__Vect___58__58_(new $HC_2_0$Builtins__MkPair("Right", new $HC_1_4$Typedefs__TVar($cg$3)), $HC_0_0$Data__Vect__Nil))));
}

// Language.JSON.Data.format, formatValue, formatProp

function Language__JSON__Data__format_58_formatValue_58_0_58_formatProp_58_3($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    
    return ((Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $partial_0_2$prim_95__95_strCons(), "", Prelude__List__replicate(null, $_3_arg.add($_4_arg), " ")) + (Language__JSON__Data__showString($_7_arg.$1) + ": ")) + Language__JSON__Data__format_58_formatValue_58_0(null, null, null, $_3_arg.add($_4_arg), $_4_arg, $_7_arg.$2));
}

// Language.JSON.Data.format, formatValue, formatProps

function Language__JSON__Data__format_58_formatValue_58_0_58_formatProps_58_3($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_arg){
    
    const $cg$3 = Prelude__List__nonEmpty(null, $_7_arg.$2);
    let $cg$2 = null;
    if(($cg$3.type === 1)) {
        $cg$2 = "\n";
    } else {
        $cg$2 = (",\n" + Language__JSON__Data__format_58_formatValue_58_0_58_formatProps_58_3(null, null, null, $_3_arg, $_4_arg, null, null, $_7_arg.$2, null));
    }
    
    return (Language__JSON__Data__format_58_formatValue_58_0_58_formatProp_58_3(null, null, null, $_3_arg, $_4_arg, null, null, $_7_arg.$1) + $cg$2);
}

// Language.JSON.Data.stringify, stringifyValues

function Language__JSON__Data__stringify_58_stringifyValues_58_4($_0_arg, $_1_arg){
    
    if(($_1_arg.type === 1)) {
        const $cg$3 = $_1_arg.$2;
        let $cg$2 = null;
        if(($cg$3.type === 1)) {
            $cg$2 = ("," + Language__JSON__Data__stringify_58_stringifyValues_58_4(null, $_1_arg.$2));
        } else {
            $cg$2 = "";
        }
        
        return (Language__JSON__Data__stringify($_1_arg.$1) + $cg$2);
    } else {
        return "";
    }
}

// Language.JSON.Data.stringify, stringifyProps

function Language__JSON__Data__stringify_58_stringifyProps_58_5($_0_arg, $_1_arg){
    
    if(($_1_arg.type === 1)) {
        const $cg$3 = $_1_arg.$1;
        let $cg$2 = null;
        $cg$2 = (Language__JSON__Data__showString($cg$3.$1) + (":" + Language__JSON__Data__stringify($cg$3.$2)));
        const $cg$5 = $_1_arg.$2;
        let $cg$4 = null;
        if(($cg$5.type === 1)) {
            $cg$4 = ("," + Language__JSON__Data__stringify_58_stringifyProps_58_5(null, $_1_arg.$2));
        } else {
            $cg$4 = "";
        }
        
        return ($cg$2 + $cg$4);
    } else {
        return "";
    }
}

// with block in Prelude.Strings.unpack

function _95_Prelude__Strings__unpack_95_with_95_36($_0_arg, $_1_arg){
    
    if(($_1_arg.type === 1)) {
        let $cg$2 = null;
        if((((($_1_arg.$2 == "")) ? 1|0 : 0|0) === 0)) {
            $cg$2 = true;
        } else {
            $cg$2 = false;
        }
        
        const $cg$4 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$2, true);
        let $cg$3 = null;
        if(($cg$4.type === 1)) {
            $cg$3 = $HC_0_0$Prelude__Strings__StrNil;
        } else {
            $cg$3 = new $HC_2_1$Prelude__Strings__StrCons($_1_arg.$2[0], $_1_arg.$2.slice(1));
        }
        
        return new $HC_2_1$Prelude__List___58__58_($_1_arg.$1, _95_Prelude__Strings__unpack_95_with_95_36(null, $cg$3));
    } else {
        return $HC_0_0$Prelude__List__Nil;
    }
}


module.exports = {
parseType: function(){ return Main__parseType.apply(this, Array.prototype.slice.call(arguments, 0,0))(arguments[0])},
generateCode: Main__generateCode
};
}.call(this))
}).call(this,require('_process'),require("buffer").Buffer)
},{"_process":7,"buffer":4,"fs":3,"os":6}],2:[function(require,module,exports){
'use strict'

exports.byteLength = byteLength
exports.toByteArray = toByteArray
exports.fromByteArray = fromByteArray

var lookup = []
var revLookup = []
var Arr = typeof Uint8Array !== 'undefined' ? Uint8Array : Array

var code = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/'
for (var i = 0, len = code.length; i < len; ++i) {
  lookup[i] = code[i]
  revLookup[code.charCodeAt(i)] = i
}

// Support decoding URL-safe base64 strings, as Node.js does.
// See: https://en.wikipedia.org/wiki/Base64#URL_applications
revLookup['-'.charCodeAt(0)] = 62
revLookup['_'.charCodeAt(0)] = 63

function getLens (b64) {
  var len = b64.length

  if (len % 4 > 0) {
    throw new Error('Invalid string. Length must be a multiple of 4')
  }

  // Trim off extra bytes after placeholder bytes are found
  // See: https://github.com/beatgammit/base64-js/issues/42
  var validLen = b64.indexOf('=')
  if (validLen === -1) validLen = len

  var placeHoldersLen = validLen === len
    ? 0
    : 4 - (validLen % 4)

  return [validLen, placeHoldersLen]
}

// base64 is 4/3 + up to two characters of the original data
function byteLength (b64) {
  var lens = getLens(b64)
  var validLen = lens[0]
  var placeHoldersLen = lens[1]
  return ((validLen + placeHoldersLen) * 3 / 4) - placeHoldersLen
}

function _byteLength (b64, validLen, placeHoldersLen) {
  return ((validLen + placeHoldersLen) * 3 / 4) - placeHoldersLen
}

function toByteArray (b64) {
  var tmp
  var lens = getLens(b64)
  var validLen = lens[0]
  var placeHoldersLen = lens[1]

  var arr = new Arr(_byteLength(b64, validLen, placeHoldersLen))

  var curByte = 0

  // if there are placeholders, only get up to the last complete 4 chars
  var len = placeHoldersLen > 0
    ? validLen - 4
    : validLen

  for (var i = 0; i < len; i += 4) {
    tmp =
      (revLookup[b64.charCodeAt(i)] << 18) |
      (revLookup[b64.charCodeAt(i + 1)] << 12) |
      (revLookup[b64.charCodeAt(i + 2)] << 6) |
      revLookup[b64.charCodeAt(i + 3)]
    arr[curByte++] = (tmp >> 16) & 0xFF
    arr[curByte++] = (tmp >> 8) & 0xFF
    arr[curByte++] = tmp & 0xFF
  }

  if (placeHoldersLen === 2) {
    tmp =
      (revLookup[b64.charCodeAt(i)] << 2) |
      (revLookup[b64.charCodeAt(i + 1)] >> 4)
    arr[curByte++] = tmp & 0xFF
  }

  if (placeHoldersLen === 1) {
    tmp =
      (revLookup[b64.charCodeAt(i)] << 10) |
      (revLookup[b64.charCodeAt(i + 1)] << 4) |
      (revLookup[b64.charCodeAt(i + 2)] >> 2)
    arr[curByte++] = (tmp >> 8) & 0xFF
    arr[curByte++] = tmp & 0xFF
  }

  return arr
}

function tripletToBase64 (num) {
  return lookup[num >> 18 & 0x3F] +
    lookup[num >> 12 & 0x3F] +
    lookup[num >> 6 & 0x3F] +
    lookup[num & 0x3F]
}

function encodeChunk (uint8, start, end) {
  var tmp
  var output = []
  for (var i = start; i < end; i += 3) {
    tmp =
      ((uint8[i] << 16) & 0xFF0000) +
      ((uint8[i + 1] << 8) & 0xFF00) +
      (uint8[i + 2] & 0xFF)
    output.push(tripletToBase64(tmp))
  }
  return output.join('')
}

function fromByteArray (uint8) {
  var tmp
  var len = uint8.length
  var extraBytes = len % 3 // if we have 1 byte left, pad 2 bytes
  var parts = []
  var maxChunkLength = 16383 // must be multiple of 3

  // go through the array every three bytes, we'll deal with trailing stuff later
  for (var i = 0, len2 = len - extraBytes; i < len2; i += maxChunkLength) {
    parts.push(encodeChunk(
      uint8, i, (i + maxChunkLength) > len2 ? len2 : (i + maxChunkLength)
    ))
  }

  // pad the end with zeros, but make sure to not forget the extra bytes
  if (extraBytes === 1) {
    tmp = uint8[len - 1]
    parts.push(
      lookup[tmp >> 2] +
      lookup[(tmp << 4) & 0x3F] +
      '=='
    )
  } else if (extraBytes === 2) {
    tmp = (uint8[len - 2] << 8) + uint8[len - 1]
    parts.push(
      lookup[tmp >> 10] +
      lookup[(tmp >> 4) & 0x3F] +
      lookup[(tmp << 2) & 0x3F] +
      '='
    )
  }

  return parts.join('')
}

},{}],3:[function(require,module,exports){

},{}],4:[function(require,module,exports){
(function (Buffer){
/*!
 * The buffer module from node.js, for the browser.
 *
 * @author   Feross Aboukhadijeh <https://feross.org>
 * @license  MIT
 */
/* eslint-disable no-proto */

'use strict'

var base64 = require('base64-js')
var ieee754 = require('ieee754')

exports.Buffer = Buffer
exports.SlowBuffer = SlowBuffer
exports.INSPECT_MAX_BYTES = 50

var K_MAX_LENGTH = 0x7fffffff
exports.kMaxLength = K_MAX_LENGTH

/**
 * If `Buffer.TYPED_ARRAY_SUPPORT`:
 *   === true    Use Uint8Array implementation (fastest)
 *   === false   Print warning and recommend using `buffer` v4.x which has an Object
 *               implementation (most compatible, even IE6)
 *
 * Browsers that support typed arrays are IE 10+, Firefox 4+, Chrome 7+, Safari 5.1+,
 * Opera 11.6+, iOS 4.2+.
 *
 * We report that the browser does not support typed arrays if the are not subclassable
 * using __proto__. Firefox 4-29 lacks support for adding new properties to `Uint8Array`
 * (See: https://bugzilla.mozilla.org/show_bug.cgi?id=695438). IE 10 lacks support
 * for __proto__ and has a buggy typed array implementation.
 */
Buffer.TYPED_ARRAY_SUPPORT = typedArraySupport()

if (!Buffer.TYPED_ARRAY_SUPPORT && typeof console !== 'undefined' &&
    typeof console.error === 'function') {
  console.error(
    'This browser lacks typed array (Uint8Array) support which is required by ' +
    '`buffer` v5.x. Use `buffer` v4.x if you require old browser support.'
  )
}

function typedArraySupport () {
  // Can typed array instances can be augmented?
  try {
    var arr = new Uint8Array(1)
    arr.__proto__ = { __proto__: Uint8Array.prototype, foo: function () { return 42 } }
    return arr.foo() === 42
  } catch (e) {
    return false
  }
}

Object.defineProperty(Buffer.prototype, 'parent', {
  enumerable: true,
  get: function () {
    if (!Buffer.isBuffer(this)) return undefined
    return this.buffer
  }
})

Object.defineProperty(Buffer.prototype, 'offset', {
  enumerable: true,
  get: function () {
    if (!Buffer.isBuffer(this)) return undefined
    return this.byteOffset
  }
})

function createBuffer (length) {
  if (length > K_MAX_LENGTH) {
    throw new RangeError('The value "' + length + '" is invalid for option "size"')
  }
  // Return an augmented `Uint8Array` instance
  var buf = new Uint8Array(length)
  buf.__proto__ = Buffer.prototype
  return buf
}

/**
 * The Buffer constructor returns instances of `Uint8Array` that have their
 * prototype changed to `Buffer.prototype`. Furthermore, `Buffer` is a subclass of
 * `Uint8Array`, so the returned instances will have all the node `Buffer` methods
 * and the `Uint8Array` methods. Square bracket notation works as expected -- it
 * returns a single octet.
 *
 * The `Uint8Array` prototype remains unmodified.
 */

function Buffer (arg, encodingOrOffset, length) {
  // Common case.
  if (typeof arg === 'number') {
    if (typeof encodingOrOffset === 'string') {
      throw new TypeError(
        'The "string" argument must be of type string. Received type number'
      )
    }
    return allocUnsafe(arg)
  }
  return from(arg, encodingOrOffset, length)
}

// Fix subarray() in ES2016. See: https://github.com/feross/buffer/pull/97
if (typeof Symbol !== 'undefined' && Symbol.species != null &&
    Buffer[Symbol.species] === Buffer) {
  Object.defineProperty(Buffer, Symbol.species, {
    value: null,
    configurable: true,
    enumerable: false,
    writable: false
  })
}

Buffer.poolSize = 8192 // not used by this implementation

function from (value, encodingOrOffset, length) {
  if (typeof value === 'string') {
    return fromString(value, encodingOrOffset)
  }

  if (ArrayBuffer.isView(value)) {
    return fromArrayLike(value)
  }

  if (value == null) {
    throw TypeError(
      'The first argument must be one of type string, Buffer, ArrayBuffer, Array, ' +
      'or Array-like Object. Received type ' + (typeof value)
    )
  }

  if (isInstance(value, ArrayBuffer) ||
      (value && isInstance(value.buffer, ArrayBuffer))) {
    return fromArrayBuffer(value, encodingOrOffset, length)
  }

  if (typeof value === 'number') {
    throw new TypeError(
      'The "value" argument must not be of type number. Received type number'
    )
  }

  var valueOf = value.valueOf && value.valueOf()
  if (valueOf != null && valueOf !== value) {
    return Buffer.from(valueOf, encodingOrOffset, length)
  }

  var b = fromObject(value)
  if (b) return b

  if (typeof Symbol !== 'undefined' && Symbol.toPrimitive != null &&
      typeof value[Symbol.toPrimitive] === 'function') {
    return Buffer.from(
      value[Symbol.toPrimitive]('string'), encodingOrOffset, length
    )
  }

  throw new TypeError(
    'The first argument must be one of type string, Buffer, ArrayBuffer, Array, ' +
    'or Array-like Object. Received type ' + (typeof value)
  )
}

/**
 * Functionally equivalent to Buffer(arg, encoding) but throws a TypeError
 * if value is a number.
 * Buffer.from(str[, encoding])
 * Buffer.from(array)
 * Buffer.from(buffer)
 * Buffer.from(arrayBuffer[, byteOffset[, length]])
 **/
Buffer.from = function (value, encodingOrOffset, length) {
  return from(value, encodingOrOffset, length)
}

// Note: Change prototype *after* Buffer.from is defined to workaround Chrome bug:
// https://github.com/feross/buffer/pull/148
Buffer.prototype.__proto__ = Uint8Array.prototype
Buffer.__proto__ = Uint8Array

function assertSize (size) {
  if (typeof size !== 'number') {
    throw new TypeError('"size" argument must be of type number')
  } else if (size < 0) {
    throw new RangeError('The value "' + size + '" is invalid for option "size"')
  }
}

function alloc (size, fill, encoding) {
  assertSize(size)
  if (size <= 0) {
    return createBuffer(size)
  }
  if (fill !== undefined) {
    // Only pay attention to encoding if it's a string. This
    // prevents accidentally sending in a number that would
    // be interpretted as a start offset.
    return typeof encoding === 'string'
      ? createBuffer(size).fill(fill, encoding)
      : createBuffer(size).fill(fill)
  }
  return createBuffer(size)
}

/**
 * Creates a new filled Buffer instance.
 * alloc(size[, fill[, encoding]])
 **/
Buffer.alloc = function (size, fill, encoding) {
  return alloc(size, fill, encoding)
}

function allocUnsafe (size) {
  assertSize(size)
  return createBuffer(size < 0 ? 0 : checked(size) | 0)
}

/**
 * Equivalent to Buffer(num), by default creates a non-zero-filled Buffer instance.
 * */
Buffer.allocUnsafe = function (size) {
  return allocUnsafe(size)
}
/**
 * Equivalent to SlowBuffer(num), by default creates a non-zero-filled Buffer instance.
 */
Buffer.allocUnsafeSlow = function (size) {
  return allocUnsafe(size)
}

function fromString (string, encoding) {
  if (typeof encoding !== 'string' || encoding === '') {
    encoding = 'utf8'
  }

  if (!Buffer.isEncoding(encoding)) {
    throw new TypeError('Unknown encoding: ' + encoding)
  }

  var length = byteLength(string, encoding) | 0
  var buf = createBuffer(length)

  var actual = buf.write(string, encoding)

  if (actual !== length) {
    // Writing a hex string, for example, that contains invalid characters will
    // cause everything after the first invalid character to be ignored. (e.g.
    // 'abxxcd' will be treated as 'ab')
    buf = buf.slice(0, actual)
  }

  return buf
}

function fromArrayLike (array) {
  var length = array.length < 0 ? 0 : checked(array.length) | 0
  var buf = createBuffer(length)
  for (var i = 0; i < length; i += 1) {
    buf[i] = array[i] & 255
  }
  return buf
}

function fromArrayBuffer (array, byteOffset, length) {
  if (byteOffset < 0 || array.byteLength < byteOffset) {
    throw new RangeError('"offset" is outside of buffer bounds')
  }

  if (array.byteLength < byteOffset + (length || 0)) {
    throw new RangeError('"length" is outside of buffer bounds')
  }

  var buf
  if (byteOffset === undefined && length === undefined) {
    buf = new Uint8Array(array)
  } else if (length === undefined) {
    buf = new Uint8Array(array, byteOffset)
  } else {
    buf = new Uint8Array(array, byteOffset, length)
  }

  // Return an augmented `Uint8Array` instance
  buf.__proto__ = Buffer.prototype
  return buf
}

function fromObject (obj) {
  if (Buffer.isBuffer(obj)) {
    var len = checked(obj.length) | 0
    var buf = createBuffer(len)

    if (buf.length === 0) {
      return buf
    }

    obj.copy(buf, 0, 0, len)
    return buf
  }

  if (obj.length !== undefined) {
    if (typeof obj.length !== 'number' || numberIsNaN(obj.length)) {
      return createBuffer(0)
    }
    return fromArrayLike(obj)
  }

  if (obj.type === 'Buffer' && Array.isArray(obj.data)) {
    return fromArrayLike(obj.data)
  }
}

function checked (length) {
  // Note: cannot use `length < K_MAX_LENGTH` here because that fails when
  // length is NaN (which is otherwise coerced to zero.)
  if (length >= K_MAX_LENGTH) {
    throw new RangeError('Attempt to allocate Buffer larger than maximum ' +
                         'size: 0x' + K_MAX_LENGTH.toString(16) + ' bytes')
  }
  return length | 0
}

function SlowBuffer (length) {
  if (+length != length) { // eslint-disable-line eqeqeq
    length = 0
  }
  return Buffer.alloc(+length)
}

Buffer.isBuffer = function isBuffer (b) {
  return b != null && b._isBuffer === true &&
    b !== Buffer.prototype // so Buffer.isBuffer(Buffer.prototype) will be false
}

Buffer.compare = function compare (a, b) {
  if (isInstance(a, Uint8Array)) a = Buffer.from(a, a.offset, a.byteLength)
  if (isInstance(b, Uint8Array)) b = Buffer.from(b, b.offset, b.byteLength)
  if (!Buffer.isBuffer(a) || !Buffer.isBuffer(b)) {
    throw new TypeError(
      'The "buf1", "buf2" arguments must be one of type Buffer or Uint8Array'
    )
  }

  if (a === b) return 0

  var x = a.length
  var y = b.length

  for (var i = 0, len = Math.min(x, y); i < len; ++i) {
    if (a[i] !== b[i]) {
      x = a[i]
      y = b[i]
      break
    }
  }

  if (x < y) return -1
  if (y < x) return 1
  return 0
}

Buffer.isEncoding = function isEncoding (encoding) {
  switch (String(encoding).toLowerCase()) {
    case 'hex':
    case 'utf8':
    case 'utf-8':
    case 'ascii':
    case 'latin1':
    case 'binary':
    case 'base64':
    case 'ucs2':
    case 'ucs-2':
    case 'utf16le':
    case 'utf-16le':
      return true
    default:
      return false
  }
}

Buffer.concat = function concat (list, length) {
  if (!Array.isArray(list)) {
    throw new TypeError('"list" argument must be an Array of Buffers')
  }

  if (list.length === 0) {
    return Buffer.alloc(0)
  }

  var i
  if (length === undefined) {
    length = 0
    for (i = 0; i < list.length; ++i) {
      length += list[i].length
    }
  }

  var buffer = Buffer.allocUnsafe(length)
  var pos = 0
  for (i = 0; i < list.length; ++i) {
    var buf = list[i]
    if (isInstance(buf, Uint8Array)) {
      buf = Buffer.from(buf)
    }
    if (!Buffer.isBuffer(buf)) {
      throw new TypeError('"list" argument must be an Array of Buffers')
    }
    buf.copy(buffer, pos)
    pos += buf.length
  }
  return buffer
}

function byteLength (string, encoding) {
  if (Buffer.isBuffer(string)) {
    return string.length
  }
  if (ArrayBuffer.isView(string) || isInstance(string, ArrayBuffer)) {
    return string.byteLength
  }
  if (typeof string !== 'string') {
    throw new TypeError(
      'The "string" argument must be one of type string, Buffer, or ArrayBuffer. ' +
      'Received type ' + typeof string
    )
  }

  var len = string.length
  var mustMatch = (arguments.length > 2 && arguments[2] === true)
  if (!mustMatch && len === 0) return 0

  // Use a for loop to avoid recursion
  var loweredCase = false
  for (;;) {
    switch (encoding) {
      case 'ascii':
      case 'latin1':
      case 'binary':
        return len
      case 'utf8':
      case 'utf-8':
        return utf8ToBytes(string).length
      case 'ucs2':
      case 'ucs-2':
      case 'utf16le':
      case 'utf-16le':
        return len * 2
      case 'hex':
        return len >>> 1
      case 'base64':
        return base64ToBytes(string).length
      default:
        if (loweredCase) {
          return mustMatch ? -1 : utf8ToBytes(string).length // assume utf8
        }
        encoding = ('' + encoding).toLowerCase()
        loweredCase = true
    }
  }
}
Buffer.byteLength = byteLength

function slowToString (encoding, start, end) {
  var loweredCase = false

  // No need to verify that "this.length <= MAX_UINT32" since it's a read-only
  // property of a typed array.

  // This behaves neither like String nor Uint8Array in that we set start/end
  // to their upper/lower bounds if the value passed is out of range.
  // undefined is handled specially as per ECMA-262 6th Edition,
  // Section 13.3.3.7 Runtime Semantics: KeyedBindingInitialization.
  if (start === undefined || start < 0) {
    start = 0
  }
  // Return early if start > this.length. Done here to prevent potential uint32
  // coercion fail below.
  if (start > this.length) {
    return ''
  }

  if (end === undefined || end > this.length) {
    end = this.length
  }

  if (end <= 0) {
    return ''
  }

  // Force coersion to uint32. This will also coerce falsey/NaN values to 0.
  end >>>= 0
  start >>>= 0

  if (end <= start) {
    return ''
  }

  if (!encoding) encoding = 'utf8'

  while (true) {
    switch (encoding) {
      case 'hex':
        return hexSlice(this, start, end)

      case 'utf8':
      case 'utf-8':
        return utf8Slice(this, start, end)

      case 'ascii':
        return asciiSlice(this, start, end)

      case 'latin1':
      case 'binary':
        return latin1Slice(this, start, end)

      case 'base64':
        return base64Slice(this, start, end)

      case 'ucs2':
      case 'ucs-2':
      case 'utf16le':
      case 'utf-16le':
        return utf16leSlice(this, start, end)

      default:
        if (loweredCase) throw new TypeError('Unknown encoding: ' + encoding)
        encoding = (encoding + '').toLowerCase()
        loweredCase = true
    }
  }
}

// This property is used by `Buffer.isBuffer` (and the `is-buffer` npm package)
// to detect a Buffer instance. It's not possible to use `instanceof Buffer`
// reliably in a browserify context because there could be multiple different
// copies of the 'buffer' package in use. This method works even for Buffer
// instances that were created from another copy of the `buffer` package.
// See: https://github.com/feross/buffer/issues/154
Buffer.prototype._isBuffer = true

function swap (b, n, m) {
  var i = b[n]
  b[n] = b[m]
  b[m] = i
}

Buffer.prototype.swap16 = function swap16 () {
  var len = this.length
  if (len % 2 !== 0) {
    throw new RangeError('Buffer size must be a multiple of 16-bits')
  }
  for (var i = 0; i < len; i += 2) {
    swap(this, i, i + 1)
  }
  return this
}

Buffer.prototype.swap32 = function swap32 () {
  var len = this.length
  if (len % 4 !== 0) {
    throw new RangeError('Buffer size must be a multiple of 32-bits')
  }
  for (var i = 0; i < len; i += 4) {
    swap(this, i, i + 3)
    swap(this, i + 1, i + 2)
  }
  return this
}

Buffer.prototype.swap64 = function swap64 () {
  var len = this.length
  if (len % 8 !== 0) {
    throw new RangeError('Buffer size must be a multiple of 64-bits')
  }
  for (var i = 0; i < len; i += 8) {
    swap(this, i, i + 7)
    swap(this, i + 1, i + 6)
    swap(this, i + 2, i + 5)
    swap(this, i + 3, i + 4)
  }
  return this
}

Buffer.prototype.toString = function toString () {
  var length = this.length
  if (length === 0) return ''
  if (arguments.length === 0) return utf8Slice(this, 0, length)
  return slowToString.apply(this, arguments)
}

Buffer.prototype.toLocaleString = Buffer.prototype.toString

Buffer.prototype.equals = function equals (b) {
  if (!Buffer.isBuffer(b)) throw new TypeError('Argument must be a Buffer')
  if (this === b) return true
  return Buffer.compare(this, b) === 0
}

Buffer.prototype.inspect = function inspect () {
  var str = ''
  var max = exports.INSPECT_MAX_BYTES
  str = this.toString('hex', 0, max).replace(/(.{2})/g, '$1 ').trim()
  if (this.length > max) str += ' ... '
  return '<Buffer ' + str + '>'
}

Buffer.prototype.compare = function compare (target, start, end, thisStart, thisEnd) {
  if (isInstance(target, Uint8Array)) {
    target = Buffer.from(target, target.offset, target.byteLength)
  }
  if (!Buffer.isBuffer(target)) {
    throw new TypeError(
      'The "target" argument must be one of type Buffer or Uint8Array. ' +
      'Received type ' + (typeof target)
    )
  }

  if (start === undefined) {
    start = 0
  }
  if (end === undefined) {
    end = target ? target.length : 0
  }
  if (thisStart === undefined) {
    thisStart = 0
  }
  if (thisEnd === undefined) {
    thisEnd = this.length
  }

  if (start < 0 || end > target.length || thisStart < 0 || thisEnd > this.length) {
    throw new RangeError('out of range index')
  }

  if (thisStart >= thisEnd && start >= end) {
    return 0
  }
  if (thisStart >= thisEnd) {
    return -1
  }
  if (start >= end) {
    return 1
  }

  start >>>= 0
  end >>>= 0
  thisStart >>>= 0
  thisEnd >>>= 0

  if (this === target) return 0

  var x = thisEnd - thisStart
  var y = end - start
  var len = Math.min(x, y)

  var thisCopy = this.slice(thisStart, thisEnd)
  var targetCopy = target.slice(start, end)

  for (var i = 0; i < len; ++i) {
    if (thisCopy[i] !== targetCopy[i]) {
      x = thisCopy[i]
      y = targetCopy[i]
      break
    }
  }

  if (x < y) return -1
  if (y < x) return 1
  return 0
}

// Finds either the first index of `val` in `buffer` at offset >= `byteOffset`,
// OR the last index of `val` in `buffer` at offset <= `byteOffset`.
//
// Arguments:
// - buffer - a Buffer to search
// - val - a string, Buffer, or number
// - byteOffset - an index into `buffer`; will be clamped to an int32
// - encoding - an optional encoding, relevant is val is a string
// - dir - true for indexOf, false for lastIndexOf
function bidirectionalIndexOf (buffer, val, byteOffset, encoding, dir) {
  // Empty buffer means no match
  if (buffer.length === 0) return -1

  // Normalize byteOffset
  if (typeof byteOffset === 'string') {
    encoding = byteOffset
    byteOffset = 0
  } else if (byteOffset > 0x7fffffff) {
    byteOffset = 0x7fffffff
  } else if (byteOffset < -0x80000000) {
    byteOffset = -0x80000000
  }
  byteOffset = +byteOffset // Coerce to Number.
  if (numberIsNaN(byteOffset)) {
    // byteOffset: it it's undefined, null, NaN, "foo", etc, search whole buffer
    byteOffset = dir ? 0 : (buffer.length - 1)
  }

  // Normalize byteOffset: negative offsets start from the end of the buffer
  if (byteOffset < 0) byteOffset = buffer.length + byteOffset
  if (byteOffset >= buffer.length) {
    if (dir) return -1
    else byteOffset = buffer.length - 1
  } else if (byteOffset < 0) {
    if (dir) byteOffset = 0
    else return -1
  }

  // Normalize val
  if (typeof val === 'string') {
    val = Buffer.from(val, encoding)
  }

  // Finally, search either indexOf (if dir is true) or lastIndexOf
  if (Buffer.isBuffer(val)) {
    // Special case: looking for empty string/buffer always fails
    if (val.length === 0) {
      return -1
    }
    return arrayIndexOf(buffer, val, byteOffset, encoding, dir)
  } else if (typeof val === 'number') {
    val = val & 0xFF // Search for a byte value [0-255]
    if (typeof Uint8Array.prototype.indexOf === 'function') {
      if (dir) {
        return Uint8Array.prototype.indexOf.call(buffer, val, byteOffset)
      } else {
        return Uint8Array.prototype.lastIndexOf.call(buffer, val, byteOffset)
      }
    }
    return arrayIndexOf(buffer, [ val ], byteOffset, encoding, dir)
  }

  throw new TypeError('val must be string, number or Buffer')
}

function arrayIndexOf (arr, val, byteOffset, encoding, dir) {
  var indexSize = 1
  var arrLength = arr.length
  var valLength = val.length

  if (encoding !== undefined) {
    encoding = String(encoding).toLowerCase()
    if (encoding === 'ucs2' || encoding === 'ucs-2' ||
        encoding === 'utf16le' || encoding === 'utf-16le') {
      if (arr.length < 2 || val.length < 2) {
        return -1
      }
      indexSize = 2
      arrLength /= 2
      valLength /= 2
      byteOffset /= 2
    }
  }

  function read (buf, i) {
    if (indexSize === 1) {
      return buf[i]
    } else {
      return buf.readUInt16BE(i * indexSize)
    }
  }

  var i
  if (dir) {
    var foundIndex = -1
    for (i = byteOffset; i < arrLength; i++) {
      if (read(arr, i) === read(val, foundIndex === -1 ? 0 : i - foundIndex)) {
        if (foundIndex === -1) foundIndex = i
        if (i - foundIndex + 1 === valLength) return foundIndex * indexSize
      } else {
        if (foundIndex !== -1) i -= i - foundIndex
        foundIndex = -1
      }
    }
  } else {
    if (byteOffset + valLength > arrLength) byteOffset = arrLength - valLength
    for (i = byteOffset; i >= 0; i--) {
      var found = true
      for (var j = 0; j < valLength; j++) {
        if (read(arr, i + j) !== read(val, j)) {
          found = false
          break
        }
      }
      if (found) return i
    }
  }

  return -1
}

Buffer.prototype.includes = function includes (val, byteOffset, encoding) {
  return this.indexOf(val, byteOffset, encoding) !== -1
}

Buffer.prototype.indexOf = function indexOf (val, byteOffset, encoding) {
  return bidirectionalIndexOf(this, val, byteOffset, encoding, true)
}

Buffer.prototype.lastIndexOf = function lastIndexOf (val, byteOffset, encoding) {
  return bidirectionalIndexOf(this, val, byteOffset, encoding, false)
}

function hexWrite (buf, string, offset, length) {
  offset = Number(offset) || 0
  var remaining = buf.length - offset
  if (!length) {
    length = remaining
  } else {
    length = Number(length)
    if (length > remaining) {
      length = remaining
    }
  }

  var strLen = string.length

  if (length > strLen / 2) {
    length = strLen / 2
  }
  for (var i = 0; i < length; ++i) {
    var parsed = parseInt(string.substr(i * 2, 2), 16)
    if (numberIsNaN(parsed)) return i
    buf[offset + i] = parsed
  }
  return i
}

function utf8Write (buf, string, offset, length) {
  return blitBuffer(utf8ToBytes(string, buf.length - offset), buf, offset, length)
}

function asciiWrite (buf, string, offset, length) {
  return blitBuffer(asciiToBytes(string), buf, offset, length)
}

function latin1Write (buf, string, offset, length) {
  return asciiWrite(buf, string, offset, length)
}

function base64Write (buf, string, offset, length) {
  return blitBuffer(base64ToBytes(string), buf, offset, length)
}

function ucs2Write (buf, string, offset, length) {
  return blitBuffer(utf16leToBytes(string, buf.length - offset), buf, offset, length)
}

Buffer.prototype.write = function write (string, offset, length, encoding) {
  // Buffer#write(string)
  if (offset === undefined) {
    encoding = 'utf8'
    length = this.length
    offset = 0
  // Buffer#write(string, encoding)
  } else if (length === undefined && typeof offset === 'string') {
    encoding = offset
    length = this.length
    offset = 0
  // Buffer#write(string, offset[, length][, encoding])
  } else if (isFinite(offset)) {
    offset = offset >>> 0
    if (isFinite(length)) {
      length = length >>> 0
      if (encoding === undefined) encoding = 'utf8'
    } else {
      encoding = length
      length = undefined
    }
  } else {
    throw new Error(
      'Buffer.write(string, encoding, offset[, length]) is no longer supported'
    )
  }

  var remaining = this.length - offset
  if (length === undefined || length > remaining) length = remaining

  if ((string.length > 0 && (length < 0 || offset < 0)) || offset > this.length) {
    throw new RangeError('Attempt to write outside buffer bounds')
  }

  if (!encoding) encoding = 'utf8'

  var loweredCase = false
  for (;;) {
    switch (encoding) {
      case 'hex':
        return hexWrite(this, string, offset, length)

      case 'utf8':
      case 'utf-8':
        return utf8Write(this, string, offset, length)

      case 'ascii':
        return asciiWrite(this, string, offset, length)

      case 'latin1':
      case 'binary':
        return latin1Write(this, string, offset, length)

      case 'base64':
        // Warning: maxLength not taken into account in base64Write
        return base64Write(this, string, offset, length)

      case 'ucs2':
      case 'ucs-2':
      case 'utf16le':
      case 'utf-16le':
        return ucs2Write(this, string, offset, length)

      default:
        if (loweredCase) throw new TypeError('Unknown encoding: ' + encoding)
        encoding = ('' + encoding).toLowerCase()
        loweredCase = true
    }
  }
}

Buffer.prototype.toJSON = function toJSON () {
  return {
    type: 'Buffer',
    data: Array.prototype.slice.call(this._arr || this, 0)
  }
}

function base64Slice (buf, start, end) {
  if (start === 0 && end === buf.length) {
    return base64.fromByteArray(buf)
  } else {
    return base64.fromByteArray(buf.slice(start, end))
  }
}

function utf8Slice (buf, start, end) {
  end = Math.min(buf.length, end)
  var res = []

  var i = start
  while (i < end) {
    var firstByte = buf[i]
    var codePoint = null
    var bytesPerSequence = (firstByte > 0xEF) ? 4
      : (firstByte > 0xDF) ? 3
        : (firstByte > 0xBF) ? 2
          : 1

    if (i + bytesPerSequence <= end) {
      var secondByte, thirdByte, fourthByte, tempCodePoint

      switch (bytesPerSequence) {
        case 1:
          if (firstByte < 0x80) {
            codePoint = firstByte
          }
          break
        case 2:
          secondByte = buf[i + 1]
          if ((secondByte & 0xC0) === 0x80) {
            tempCodePoint = (firstByte & 0x1F) << 0x6 | (secondByte & 0x3F)
            if (tempCodePoint > 0x7F) {
              codePoint = tempCodePoint
            }
          }
          break
        case 3:
          secondByte = buf[i + 1]
          thirdByte = buf[i + 2]
          if ((secondByte & 0xC0) === 0x80 && (thirdByte & 0xC0) === 0x80) {
            tempCodePoint = (firstByte & 0xF) << 0xC | (secondByte & 0x3F) << 0x6 | (thirdByte & 0x3F)
            if (tempCodePoint > 0x7FF && (tempCodePoint < 0xD800 || tempCodePoint > 0xDFFF)) {
              codePoint = tempCodePoint
            }
          }
          break
        case 4:
          secondByte = buf[i + 1]
          thirdByte = buf[i + 2]
          fourthByte = buf[i + 3]
          if ((secondByte & 0xC0) === 0x80 && (thirdByte & 0xC0) === 0x80 && (fourthByte & 0xC0) === 0x80) {
            tempCodePoint = (firstByte & 0xF) << 0x12 | (secondByte & 0x3F) << 0xC | (thirdByte & 0x3F) << 0x6 | (fourthByte & 0x3F)
            if (tempCodePoint > 0xFFFF && tempCodePoint < 0x110000) {
              codePoint = tempCodePoint
            }
          }
      }
    }

    if (codePoint === null) {
      // we did not generate a valid codePoint so insert a
      // replacement char (U+FFFD) and advance only 1 byte
      codePoint = 0xFFFD
      bytesPerSequence = 1
    } else if (codePoint > 0xFFFF) {
      // encode to utf16 (surrogate pair dance)
      codePoint -= 0x10000
      res.push(codePoint >>> 10 & 0x3FF | 0xD800)
      codePoint = 0xDC00 | codePoint & 0x3FF
    }

    res.push(codePoint)
    i += bytesPerSequence
  }

  return decodeCodePointsArray(res)
}

// Based on http://stackoverflow.com/a/22747272/680742, the browser with
// the lowest limit is Chrome, with 0x10000 args.
// We go 1 magnitude less, for safety
var MAX_ARGUMENTS_LENGTH = 0x1000

function decodeCodePointsArray (codePoints) {
  var len = codePoints.length
  if (len <= MAX_ARGUMENTS_LENGTH) {
    return String.fromCharCode.apply(String, codePoints) // avoid extra slice()
  }

  // Decode in chunks to avoid "call stack size exceeded".
  var res = ''
  var i = 0
  while (i < len) {
    res += String.fromCharCode.apply(
      String,
      codePoints.slice(i, i += MAX_ARGUMENTS_LENGTH)
    )
  }
  return res
}

function asciiSlice (buf, start, end) {
  var ret = ''
  end = Math.min(buf.length, end)

  for (var i = start; i < end; ++i) {
    ret += String.fromCharCode(buf[i] & 0x7F)
  }
  return ret
}

function latin1Slice (buf, start, end) {
  var ret = ''
  end = Math.min(buf.length, end)

  for (var i = start; i < end; ++i) {
    ret += String.fromCharCode(buf[i])
  }
  return ret
}

function hexSlice (buf, start, end) {
  var len = buf.length

  if (!start || start < 0) start = 0
  if (!end || end < 0 || end > len) end = len

  var out = ''
  for (var i = start; i < end; ++i) {
    out += toHex(buf[i])
  }
  return out
}

function utf16leSlice (buf, start, end) {
  var bytes = buf.slice(start, end)
  var res = ''
  for (var i = 0; i < bytes.length; i += 2) {
    res += String.fromCharCode(bytes[i] + (bytes[i + 1] * 256))
  }
  return res
}

Buffer.prototype.slice = function slice (start, end) {
  var len = this.length
  start = ~~start
  end = end === undefined ? len : ~~end

  if (start < 0) {
    start += len
    if (start < 0) start = 0
  } else if (start > len) {
    start = len
  }

  if (end < 0) {
    end += len
    if (end < 0) end = 0
  } else if (end > len) {
    end = len
  }

  if (end < start) end = start

  var newBuf = this.subarray(start, end)
  // Return an augmented `Uint8Array` instance
  newBuf.__proto__ = Buffer.prototype
  return newBuf
}

/*
 * Need to make sure that buffer isn't trying to write out of bounds.
 */
function checkOffset (offset, ext, length) {
  if ((offset % 1) !== 0 || offset < 0) throw new RangeError('offset is not uint')
  if (offset + ext > length) throw new RangeError('Trying to access beyond buffer length')
}

Buffer.prototype.readUIntLE = function readUIntLE (offset, byteLength, noAssert) {
  offset = offset >>> 0
  byteLength = byteLength >>> 0
  if (!noAssert) checkOffset(offset, byteLength, this.length)

  var val = this[offset]
  var mul = 1
  var i = 0
  while (++i < byteLength && (mul *= 0x100)) {
    val += this[offset + i] * mul
  }

  return val
}

Buffer.prototype.readUIntBE = function readUIntBE (offset, byteLength, noAssert) {
  offset = offset >>> 0
  byteLength = byteLength >>> 0
  if (!noAssert) {
    checkOffset(offset, byteLength, this.length)
  }

  var val = this[offset + --byteLength]
  var mul = 1
  while (byteLength > 0 && (mul *= 0x100)) {
    val += this[offset + --byteLength] * mul
  }

  return val
}

Buffer.prototype.readUInt8 = function readUInt8 (offset, noAssert) {
  offset = offset >>> 0
  if (!noAssert) checkOffset(offset, 1, this.length)
  return this[offset]
}

Buffer.prototype.readUInt16LE = function readUInt16LE (offset, noAssert) {
  offset = offset >>> 0
  if (!noAssert) checkOffset(offset, 2, this.length)
  return this[offset] | (this[offset + 1] << 8)
}

Buffer.prototype.readUInt16BE = function readUInt16BE (offset, noAssert) {
  offset = offset >>> 0
  if (!noAssert) checkOffset(offset, 2, this.length)
  return (this[offset] << 8) | this[offset + 1]
}

Buffer.prototype.readUInt32LE = function readUInt32LE (offset, noAssert) {
  offset = offset >>> 0
  if (!noAssert) checkOffset(offset, 4, this.length)

  return ((this[offset]) |
      (this[offset + 1] << 8) |
      (this[offset + 2] << 16)) +
      (this[offset + 3] * 0x1000000)
}

Buffer.prototype.readUInt32BE = function readUInt32BE (offset, noAssert) {
  offset = offset >>> 0
  if (!noAssert) checkOffset(offset, 4, this.length)

  return (this[offset] * 0x1000000) +
    ((this[offset + 1] << 16) |
    (this[offset + 2] << 8) |
    this[offset + 3])
}

Buffer.prototype.readIntLE = function readIntLE (offset, byteLength, noAssert) {
  offset = offset >>> 0
  byteLength = byteLength >>> 0
  if (!noAssert) checkOffset(offset, byteLength, this.length)

  var val = this[offset]
  var mul = 1
  var i = 0
  while (++i < byteLength && (mul *= 0x100)) {
    val += this[offset + i] * mul
  }
  mul *= 0x80

  if (val >= mul) val -= Math.pow(2, 8 * byteLength)

  return val
}

Buffer.prototype.readIntBE = function readIntBE (offset, byteLength, noAssert) {
  offset = offset >>> 0
  byteLength = byteLength >>> 0
  if (!noAssert) checkOffset(offset, byteLength, this.length)

  var i = byteLength
  var mul = 1
  var val = this[offset + --i]
  while (i > 0 && (mul *= 0x100)) {
    val += this[offset + --i] * mul
  }
  mul *= 0x80

  if (val >= mul) val -= Math.pow(2, 8 * byteLength)

  return val
}

Buffer.prototype.readInt8 = function readInt8 (offset, noAssert) {
  offset = offset >>> 0
  if (!noAssert) checkOffset(offset, 1, this.length)
  if (!(this[offset] & 0x80)) return (this[offset])
  return ((0xff - this[offset] + 1) * -1)
}

Buffer.prototype.readInt16LE = function readInt16LE (offset, noAssert) {
  offset = offset >>> 0
  if (!noAssert) checkOffset(offset, 2, this.length)
  var val = this[offset] | (this[offset + 1] << 8)
  return (val & 0x8000) ? val | 0xFFFF0000 : val
}

Buffer.prototype.readInt16BE = function readInt16BE (offset, noAssert) {
  offset = offset >>> 0
  if (!noAssert) checkOffset(offset, 2, this.length)
  var val = this[offset + 1] | (this[offset] << 8)
  return (val & 0x8000) ? val | 0xFFFF0000 : val
}

Buffer.prototype.readInt32LE = function readInt32LE (offset, noAssert) {
  offset = offset >>> 0
  if (!noAssert) checkOffset(offset, 4, this.length)

  return (this[offset]) |
    (this[offset + 1] << 8) |
    (this[offset + 2] << 16) |
    (this[offset + 3] << 24)
}

Buffer.prototype.readInt32BE = function readInt32BE (offset, noAssert) {
  offset = offset >>> 0
  if (!noAssert) checkOffset(offset, 4, this.length)

  return (this[offset] << 24) |
    (this[offset + 1] << 16) |
    (this[offset + 2] << 8) |
    (this[offset + 3])
}

Buffer.prototype.readFloatLE = function readFloatLE (offset, noAssert) {
  offset = offset >>> 0
  if (!noAssert) checkOffset(offset, 4, this.length)
  return ieee754.read(this, offset, true, 23, 4)
}

Buffer.prototype.readFloatBE = function readFloatBE (offset, noAssert) {
  offset = offset >>> 0
  if (!noAssert) checkOffset(offset, 4, this.length)
  return ieee754.read(this, offset, false, 23, 4)
}

Buffer.prototype.readDoubleLE = function readDoubleLE (offset, noAssert) {
  offset = offset >>> 0
  if (!noAssert) checkOffset(offset, 8, this.length)
  return ieee754.read(this, offset, true, 52, 8)
}

Buffer.prototype.readDoubleBE = function readDoubleBE (offset, noAssert) {
  offset = offset >>> 0
  if (!noAssert) checkOffset(offset, 8, this.length)
  return ieee754.read(this, offset, false, 52, 8)
}

function checkInt (buf, value, offset, ext, max, min) {
  if (!Buffer.isBuffer(buf)) throw new TypeError('"buffer" argument must be a Buffer instance')
  if (value > max || value < min) throw new RangeError('"value" argument is out of bounds')
  if (offset + ext > buf.length) throw new RangeError('Index out of range')
}

Buffer.prototype.writeUIntLE = function writeUIntLE (value, offset, byteLength, noAssert) {
  value = +value
  offset = offset >>> 0
  byteLength = byteLength >>> 0
  if (!noAssert) {
    var maxBytes = Math.pow(2, 8 * byteLength) - 1
    checkInt(this, value, offset, byteLength, maxBytes, 0)
  }

  var mul = 1
  var i = 0
  this[offset] = value & 0xFF
  while (++i < byteLength && (mul *= 0x100)) {
    this[offset + i] = (value / mul) & 0xFF
  }

  return offset + byteLength
}

Buffer.prototype.writeUIntBE = function writeUIntBE (value, offset, byteLength, noAssert) {
  value = +value
  offset = offset >>> 0
  byteLength = byteLength >>> 0
  if (!noAssert) {
    var maxBytes = Math.pow(2, 8 * byteLength) - 1
    checkInt(this, value, offset, byteLength, maxBytes, 0)
  }

  var i = byteLength - 1
  var mul = 1
  this[offset + i] = value & 0xFF
  while (--i >= 0 && (mul *= 0x100)) {
    this[offset + i] = (value / mul) & 0xFF
  }

  return offset + byteLength
}

Buffer.prototype.writeUInt8 = function writeUInt8 (value, offset, noAssert) {
  value = +value
  offset = offset >>> 0
  if (!noAssert) checkInt(this, value, offset, 1, 0xff, 0)
  this[offset] = (value & 0xff)
  return offset + 1
}

Buffer.prototype.writeUInt16LE = function writeUInt16LE (value, offset, noAssert) {
  value = +value
  offset = offset >>> 0
  if (!noAssert) checkInt(this, value, offset, 2, 0xffff, 0)
  this[offset] = (value & 0xff)
  this[offset + 1] = (value >>> 8)
  return offset + 2
}

Buffer.prototype.writeUInt16BE = function writeUInt16BE (value, offset, noAssert) {
  value = +value
  offset = offset >>> 0
  if (!noAssert) checkInt(this, value, offset, 2, 0xffff, 0)
  this[offset] = (value >>> 8)
  this[offset + 1] = (value & 0xff)
  return offset + 2
}

Buffer.prototype.writeUInt32LE = function writeUInt32LE (value, offset, noAssert) {
  value = +value
  offset = offset >>> 0
  if (!noAssert) checkInt(this, value, offset, 4, 0xffffffff, 0)
  this[offset + 3] = (value >>> 24)
  this[offset + 2] = (value >>> 16)
  this[offset + 1] = (value >>> 8)
  this[offset] = (value & 0xff)
  return offset + 4
}

Buffer.prototype.writeUInt32BE = function writeUInt32BE (value, offset, noAssert) {
  value = +value
  offset = offset >>> 0
  if (!noAssert) checkInt(this, value, offset, 4, 0xffffffff, 0)
  this[offset] = (value >>> 24)
  this[offset + 1] = (value >>> 16)
  this[offset + 2] = (value >>> 8)
  this[offset + 3] = (value & 0xff)
  return offset + 4
}

Buffer.prototype.writeIntLE = function writeIntLE (value, offset, byteLength, noAssert) {
  value = +value
  offset = offset >>> 0
  if (!noAssert) {
    var limit = Math.pow(2, (8 * byteLength) - 1)

    checkInt(this, value, offset, byteLength, limit - 1, -limit)
  }

  var i = 0
  var mul = 1
  var sub = 0
  this[offset] = value & 0xFF
  while (++i < byteLength && (mul *= 0x100)) {
    if (value < 0 && sub === 0 && this[offset + i - 1] !== 0) {
      sub = 1
    }
    this[offset + i] = ((value / mul) >> 0) - sub & 0xFF
  }

  return offset + byteLength
}

Buffer.prototype.writeIntBE = function writeIntBE (value, offset, byteLength, noAssert) {
  value = +value
  offset = offset >>> 0
  if (!noAssert) {
    var limit = Math.pow(2, (8 * byteLength) - 1)

    checkInt(this, value, offset, byteLength, limit - 1, -limit)
  }

  var i = byteLength - 1
  var mul = 1
  var sub = 0
  this[offset + i] = value & 0xFF
  while (--i >= 0 && (mul *= 0x100)) {
    if (value < 0 && sub === 0 && this[offset + i + 1] !== 0) {
      sub = 1
    }
    this[offset + i] = ((value / mul) >> 0) - sub & 0xFF
  }

  return offset + byteLength
}

Buffer.prototype.writeInt8 = function writeInt8 (value, offset, noAssert) {
  value = +value
  offset = offset >>> 0
  if (!noAssert) checkInt(this, value, offset, 1, 0x7f, -0x80)
  if (value < 0) value = 0xff + value + 1
  this[offset] = (value & 0xff)
  return offset + 1
}

Buffer.prototype.writeInt16LE = function writeInt16LE (value, offset, noAssert) {
  value = +value
  offset = offset >>> 0
  if (!noAssert) checkInt(this, value, offset, 2, 0x7fff, -0x8000)
  this[offset] = (value & 0xff)
  this[offset + 1] = (value >>> 8)
  return offset + 2
}

Buffer.prototype.writeInt16BE = function writeInt16BE (value, offset, noAssert) {
  value = +value
  offset = offset >>> 0
  if (!noAssert) checkInt(this, value, offset, 2, 0x7fff, -0x8000)
  this[offset] = (value >>> 8)
  this[offset + 1] = (value & 0xff)
  return offset + 2
}

Buffer.prototype.writeInt32LE = function writeInt32LE (value, offset, noAssert) {
  value = +value
  offset = offset >>> 0
  if (!noAssert) checkInt(this, value, offset, 4, 0x7fffffff, -0x80000000)
  this[offset] = (value & 0xff)
  this[offset + 1] = (value >>> 8)
  this[offset + 2] = (value >>> 16)
  this[offset + 3] = (value >>> 24)
  return offset + 4
}

Buffer.prototype.writeInt32BE = function writeInt32BE (value, offset, noAssert) {
  value = +value
  offset = offset >>> 0
  if (!noAssert) checkInt(this, value, offset, 4, 0x7fffffff, -0x80000000)
  if (value < 0) value = 0xffffffff + value + 1
  this[offset] = (value >>> 24)
  this[offset + 1] = (value >>> 16)
  this[offset + 2] = (value >>> 8)
  this[offset + 3] = (value & 0xff)
  return offset + 4
}

function checkIEEE754 (buf, value, offset, ext, max, min) {
  if (offset + ext > buf.length) throw new RangeError('Index out of range')
  if (offset < 0) throw new RangeError('Index out of range')
}

function writeFloat (buf, value, offset, littleEndian, noAssert) {
  value = +value
  offset = offset >>> 0
  if (!noAssert) {
    checkIEEE754(buf, value, offset, 4, 3.4028234663852886e+38, -3.4028234663852886e+38)
  }
  ieee754.write(buf, value, offset, littleEndian, 23, 4)
  return offset + 4
}

Buffer.prototype.writeFloatLE = function writeFloatLE (value, offset, noAssert) {
  return writeFloat(this, value, offset, true, noAssert)
}

Buffer.prototype.writeFloatBE = function writeFloatBE (value, offset, noAssert) {
  return writeFloat(this, value, offset, false, noAssert)
}

function writeDouble (buf, value, offset, littleEndian, noAssert) {
  value = +value
  offset = offset >>> 0
  if (!noAssert) {
    checkIEEE754(buf, value, offset, 8, 1.7976931348623157E+308, -1.7976931348623157E+308)
  }
  ieee754.write(buf, value, offset, littleEndian, 52, 8)
  return offset + 8
}

Buffer.prototype.writeDoubleLE = function writeDoubleLE (value, offset, noAssert) {
  return writeDouble(this, value, offset, true, noAssert)
}

Buffer.prototype.writeDoubleBE = function writeDoubleBE (value, offset, noAssert) {
  return writeDouble(this, value, offset, false, noAssert)
}

// copy(targetBuffer, targetStart=0, sourceStart=0, sourceEnd=buffer.length)
Buffer.prototype.copy = function copy (target, targetStart, start, end) {
  if (!Buffer.isBuffer(target)) throw new TypeError('argument should be a Buffer')
  if (!start) start = 0
  if (!end && end !== 0) end = this.length
  if (targetStart >= target.length) targetStart = target.length
  if (!targetStart) targetStart = 0
  if (end > 0 && end < start) end = start

  // Copy 0 bytes; we're done
  if (end === start) return 0
  if (target.length === 0 || this.length === 0) return 0

  // Fatal error conditions
  if (targetStart < 0) {
    throw new RangeError('targetStart out of bounds')
  }
  if (start < 0 || start >= this.length) throw new RangeError('Index out of range')
  if (end < 0) throw new RangeError('sourceEnd out of bounds')

  // Are we oob?
  if (end > this.length) end = this.length
  if (target.length - targetStart < end - start) {
    end = target.length - targetStart + start
  }

  var len = end - start

  if (this === target && typeof Uint8Array.prototype.copyWithin === 'function') {
    // Use built-in when available, missing from IE11
    this.copyWithin(targetStart, start, end)
  } else if (this === target && start < targetStart && targetStart < end) {
    // descending copy from end
    for (var i = len - 1; i >= 0; --i) {
      target[i + targetStart] = this[i + start]
    }
  } else {
    Uint8Array.prototype.set.call(
      target,
      this.subarray(start, end),
      targetStart
    )
  }

  return len
}

// Usage:
//    buffer.fill(number[, offset[, end]])
//    buffer.fill(buffer[, offset[, end]])
//    buffer.fill(string[, offset[, end]][, encoding])
Buffer.prototype.fill = function fill (val, start, end, encoding) {
  // Handle string cases:
  if (typeof val === 'string') {
    if (typeof start === 'string') {
      encoding = start
      start = 0
      end = this.length
    } else if (typeof end === 'string') {
      encoding = end
      end = this.length
    }
    if (encoding !== undefined && typeof encoding !== 'string') {
      throw new TypeError('encoding must be a string')
    }
    if (typeof encoding === 'string' && !Buffer.isEncoding(encoding)) {
      throw new TypeError('Unknown encoding: ' + encoding)
    }
    if (val.length === 1) {
      var code = val.charCodeAt(0)
      if ((encoding === 'utf8' && code < 128) ||
          encoding === 'latin1') {
        // Fast path: If `val` fits into a single byte, use that numeric value.
        val = code
      }
    }
  } else if (typeof val === 'number') {
    val = val & 255
  }

  // Invalid ranges are not set to a default, so can range check early.
  if (start < 0 || this.length < start || this.length < end) {
    throw new RangeError('Out of range index')
  }

  if (end <= start) {
    return this
  }

  start = start >>> 0
  end = end === undefined ? this.length : end >>> 0

  if (!val) val = 0

  var i
  if (typeof val === 'number') {
    for (i = start; i < end; ++i) {
      this[i] = val
    }
  } else {
    var bytes = Buffer.isBuffer(val)
      ? val
      : Buffer.from(val, encoding)
    var len = bytes.length
    if (len === 0) {
      throw new TypeError('The value "' + val +
        '" is invalid for argument "value"')
    }
    for (i = 0; i < end - start; ++i) {
      this[i + start] = bytes[i % len]
    }
  }

  return this
}

// HELPER FUNCTIONS
// ================

var INVALID_BASE64_RE = /[^+/0-9A-Za-z-_]/g

function base64clean (str) {
  // Node takes equal signs as end of the Base64 encoding
  str = str.split('=')[0]
  // Node strips out invalid characters like \n and \t from the string, base64-js does not
  str = str.trim().replace(INVALID_BASE64_RE, '')
  // Node converts strings with length < 2 to ''
  if (str.length < 2) return ''
  // Node allows for non-padded base64 strings (missing trailing ===), base64-js does not
  while (str.length % 4 !== 0) {
    str = str + '='
  }
  return str
}

function toHex (n) {
  if (n < 16) return '0' + n.toString(16)
  return n.toString(16)
}

function utf8ToBytes (string, units) {
  units = units || Infinity
  var codePoint
  var length = string.length
  var leadSurrogate = null
  var bytes = []

  for (var i = 0; i < length; ++i) {
    codePoint = string.charCodeAt(i)

    // is surrogate component
    if (codePoint > 0xD7FF && codePoint < 0xE000) {
      // last char was a lead
      if (!leadSurrogate) {
        // no lead yet
        if (codePoint > 0xDBFF) {
          // unexpected trail
          if ((units -= 3) > -1) bytes.push(0xEF, 0xBF, 0xBD)
          continue
        } else if (i + 1 === length) {
          // unpaired lead
          if ((units -= 3) > -1) bytes.push(0xEF, 0xBF, 0xBD)
          continue
        }

        // valid lead
        leadSurrogate = codePoint

        continue
      }

      // 2 leads in a row
      if (codePoint < 0xDC00) {
        if ((units -= 3) > -1) bytes.push(0xEF, 0xBF, 0xBD)
        leadSurrogate = codePoint
        continue
      }

      // valid surrogate pair
      codePoint = (leadSurrogate - 0xD800 << 10 | codePoint - 0xDC00) + 0x10000
    } else if (leadSurrogate) {
      // valid bmp char, but last char was a lead
      if ((units -= 3) > -1) bytes.push(0xEF, 0xBF, 0xBD)
    }

    leadSurrogate = null

    // encode utf8
    if (codePoint < 0x80) {
      if ((units -= 1) < 0) break
      bytes.push(codePoint)
    } else if (codePoint < 0x800) {
      if ((units -= 2) < 0) break
      bytes.push(
        codePoint >> 0x6 | 0xC0,
        codePoint & 0x3F | 0x80
      )
    } else if (codePoint < 0x10000) {
      if ((units -= 3) < 0) break
      bytes.push(
        codePoint >> 0xC | 0xE0,
        codePoint >> 0x6 & 0x3F | 0x80,
        codePoint & 0x3F | 0x80
      )
    } else if (codePoint < 0x110000) {
      if ((units -= 4) < 0) break
      bytes.push(
        codePoint >> 0x12 | 0xF0,
        codePoint >> 0xC & 0x3F | 0x80,
        codePoint >> 0x6 & 0x3F | 0x80,
        codePoint & 0x3F | 0x80
      )
    } else {
      throw new Error('Invalid code point')
    }
  }

  return bytes
}

function asciiToBytes (str) {
  var byteArray = []
  for (var i = 0; i < str.length; ++i) {
    // Node's code seems to be doing this and not & 0x7F..
    byteArray.push(str.charCodeAt(i) & 0xFF)
  }
  return byteArray
}

function utf16leToBytes (str, units) {
  var c, hi, lo
  var byteArray = []
  for (var i = 0; i < str.length; ++i) {
    if ((units -= 2) < 0) break

    c = str.charCodeAt(i)
    hi = c >> 8
    lo = c % 256
    byteArray.push(lo)
    byteArray.push(hi)
  }

  return byteArray
}

function base64ToBytes (str) {
  return base64.toByteArray(base64clean(str))
}

function blitBuffer (src, dst, offset, length) {
  for (var i = 0; i < length; ++i) {
    if ((i + offset >= dst.length) || (i >= src.length)) break
    dst[i + offset] = src[i]
  }
  return i
}

// ArrayBuffer or Uint8Array objects from other contexts (i.e. iframes) do not pass
// the `instanceof` check but they should be treated as of that type.
// See: https://github.com/feross/buffer/issues/166
function isInstance (obj, type) {
  return obj instanceof type ||
    (obj != null && obj.constructor != null && obj.constructor.name != null &&
      obj.constructor.name === type.name)
}
function numberIsNaN (obj) {
  // For IE11 support
  return obj !== obj // eslint-disable-line no-self-compare
}

}).call(this,require("buffer").Buffer)
},{"base64-js":2,"buffer":4,"ieee754":5}],5:[function(require,module,exports){
exports.read = function (buffer, offset, isLE, mLen, nBytes) {
  var e, m
  var eLen = (nBytes * 8) - mLen - 1
  var eMax = (1 << eLen) - 1
  var eBias = eMax >> 1
  var nBits = -7
  var i = isLE ? (nBytes - 1) : 0
  var d = isLE ? -1 : 1
  var s = buffer[offset + i]

  i += d

  e = s & ((1 << (-nBits)) - 1)
  s >>= (-nBits)
  nBits += eLen
  for (; nBits > 0; e = (e * 256) + buffer[offset + i], i += d, nBits -= 8) {}

  m = e & ((1 << (-nBits)) - 1)
  e >>= (-nBits)
  nBits += mLen
  for (; nBits > 0; m = (m * 256) + buffer[offset + i], i += d, nBits -= 8) {}

  if (e === 0) {
    e = 1 - eBias
  } else if (e === eMax) {
    return m ? NaN : ((s ? -1 : 1) * Infinity)
  } else {
    m = m + Math.pow(2, mLen)
    e = e - eBias
  }
  return (s ? -1 : 1) * m * Math.pow(2, e - mLen)
}

exports.write = function (buffer, value, offset, isLE, mLen, nBytes) {
  var e, m, c
  var eLen = (nBytes * 8) - mLen - 1
  var eMax = (1 << eLen) - 1
  var eBias = eMax >> 1
  var rt = (mLen === 23 ? Math.pow(2, -24) - Math.pow(2, -77) : 0)
  var i = isLE ? 0 : (nBytes - 1)
  var d = isLE ? 1 : -1
  var s = value < 0 || (value === 0 && 1 / value < 0) ? 1 : 0

  value = Math.abs(value)

  if (isNaN(value) || value === Infinity) {
    m = isNaN(value) ? 1 : 0
    e = eMax
  } else {
    e = Math.floor(Math.log(value) / Math.LN2)
    if (value * (c = Math.pow(2, -e)) < 1) {
      e--
      c *= 2
    }
    if (e + eBias >= 1) {
      value += rt / c
    } else {
      value += rt * Math.pow(2, 1 - eBias)
    }
    if (value * c >= 2) {
      e++
      c /= 2
    }

    if (e + eBias >= eMax) {
      m = 0
      e = eMax
    } else if (e + eBias >= 1) {
      m = ((value * c) - 1) * Math.pow(2, mLen)
      e = e + eBias
    } else {
      m = value * Math.pow(2, eBias - 1) * Math.pow(2, mLen)
      e = 0
    }
  }

  for (; mLen >= 8; buffer[offset + i] = m & 0xff, i += d, m /= 256, mLen -= 8) {}

  e = (e << mLen) | m
  eLen += mLen
  for (; eLen > 0; buffer[offset + i] = e & 0xff, i += d, e /= 256, eLen -= 8) {}

  buffer[offset + i - d] |= s * 128
}

},{}],6:[function(require,module,exports){
exports.endianness = function () { return 'LE' };

exports.hostname = function () {
    if (typeof location !== 'undefined') {
        return location.hostname
    }
    else return '';
};

exports.loadavg = function () { return [] };

exports.uptime = function () { return 0 };

exports.freemem = function () {
    return Number.MAX_VALUE;
};

exports.totalmem = function () {
    return Number.MAX_VALUE;
};

exports.cpus = function () { return [] };

exports.type = function () { return 'Browser' };

exports.release = function () {
    if (typeof navigator !== 'undefined') {
        return navigator.appVersion;
    }
    return '';
};

exports.networkInterfaces
= exports.getNetworkInterfaces
= function () { return {} };

exports.arch = function () { return 'javascript' };

exports.platform = function () { return 'browser' };

exports.tmpdir = exports.tmpDir = function () {
    return '/tmp';
};

exports.EOL = '\n';

exports.homedir = function () {
	return '/'
};

},{}],7:[function(require,module,exports){
// shim for using process in browser
var process = module.exports = {};

// cached from whatever global is present so that test runners that stub it
// don't break things.  But we need to wrap it in a try catch in case it is
// wrapped in strict mode code which doesn't define any globals.  It's inside a
// function because try/catches deoptimize in certain engines.

var cachedSetTimeout;
var cachedClearTimeout;

function defaultSetTimout() {
    throw new Error('setTimeout has not been defined');
}
function defaultClearTimeout () {
    throw new Error('clearTimeout has not been defined');
}
(function () {
    try {
        if (typeof setTimeout === 'function') {
            cachedSetTimeout = setTimeout;
        } else {
            cachedSetTimeout = defaultSetTimout;
        }
    } catch (e) {
        cachedSetTimeout = defaultSetTimout;
    }
    try {
        if (typeof clearTimeout === 'function') {
            cachedClearTimeout = clearTimeout;
        } else {
            cachedClearTimeout = defaultClearTimeout;
        }
    } catch (e) {
        cachedClearTimeout = defaultClearTimeout;
    }
} ())
function runTimeout(fun) {
    if (cachedSetTimeout === setTimeout) {
        //normal enviroments in sane situations
        return setTimeout(fun, 0);
    }
    // if setTimeout wasn't available but was latter defined
    if ((cachedSetTimeout === defaultSetTimout || !cachedSetTimeout) && setTimeout) {
        cachedSetTimeout = setTimeout;
        return setTimeout(fun, 0);
    }
    try {
        // when when somebody has screwed with setTimeout but no I.E. maddness
        return cachedSetTimeout(fun, 0);
    } catch(e){
        try {
            // When we are in I.E. but the script has been evaled so I.E. doesn't trust the global object when called normally
            return cachedSetTimeout.call(null, fun, 0);
        } catch(e){
            // same as above but when it's a version of I.E. that must have the global object for 'this', hopfully our context correct otherwise it will throw a global error
            return cachedSetTimeout.call(this, fun, 0);
        }
    }


}
function runClearTimeout(marker) {
    if (cachedClearTimeout === clearTimeout) {
        //normal enviroments in sane situations
        return clearTimeout(marker);
    }
    // if clearTimeout wasn't available but was latter defined
    if ((cachedClearTimeout === defaultClearTimeout || !cachedClearTimeout) && clearTimeout) {
        cachedClearTimeout = clearTimeout;
        return clearTimeout(marker);
    }
    try {
        // when when somebody has screwed with setTimeout but no I.E. maddness
        return cachedClearTimeout(marker);
    } catch (e){
        try {
            // When we are in I.E. but the script has been evaled so I.E. doesn't  trust the global object when called normally
            return cachedClearTimeout.call(null, marker);
        } catch (e){
            // same as above but when it's a version of I.E. that must have the global object for 'this', hopfully our context correct otherwise it will throw a global error.
            // Some versions of I.E. have different rules for clearTimeout vs setTimeout
            return cachedClearTimeout.call(this, marker);
        }
    }



}
var queue = [];
var draining = false;
var currentQueue;
var queueIndex = -1;

function cleanUpNextTick() {
    if (!draining || !currentQueue) {
        return;
    }
    draining = false;
    if (currentQueue.length) {
        queue = currentQueue.concat(queue);
    } else {
        queueIndex = -1;
    }
    if (queue.length) {
        drainQueue();
    }
}

function drainQueue() {
    if (draining) {
        return;
    }
    var timeout = runTimeout(cleanUpNextTick);
    draining = true;

    var len = queue.length;
    while(len) {
        currentQueue = queue;
        queue = [];
        while (++queueIndex < len) {
            if (currentQueue) {
                currentQueue[queueIndex].run();
            }
        }
        queueIndex = -1;
        len = queue.length;
    }
    currentQueue = null;
    draining = false;
    runClearTimeout(timeout);
}

process.nextTick = function (fun) {
    var args = new Array(arguments.length - 1);
    if (arguments.length > 1) {
        for (var i = 1; i < arguments.length; i++) {
            args[i - 1] = arguments[i];
        }
    }
    queue.push(new Item(fun, args));
    if (queue.length === 1 && !draining) {
        runTimeout(drainQueue);
    }
};

// v8 likes predictible objects
function Item(fun, array) {
    this.fun = fun;
    this.array = array;
}
Item.prototype.run = function () {
    this.fun.apply(null, this.array);
};
process.title = 'browser';
process.browser = true;
process.env = {};
process.argv = [];
process.version = ''; // empty string to avoid regexp issues
process.versions = {};

function noop() {}

process.on = noop;
process.addListener = noop;
process.once = noop;
process.off = noop;
process.removeListener = noop;
process.removeAllListeners = noop;
process.emit = noop;
process.prependListener = noop;
process.prependOnceListener = noop;

process.listeners = function (name) { return [] }

process.binding = function (name) {
    throw new Error('process.binding is not supported');
};

process.cwd = function () { return '/' };
process.chdir = function (dir) {
    throw new Error('process.chdir is not supported');
};
process.umask = function() { return 0; };

},{}],8:[function(require,module,exports){
// this allows us to bundle Typedefs javascript module and exposes it as a
// global variable so we can use it from the browser.
window.Typedefs = require('../lib/typedefs.js')

},{"../lib/typedefs.js":1}]},{},[8]);
