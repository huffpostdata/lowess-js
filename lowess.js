// Source: http://www.stat.washington.edu/courses/stat527/s13/readings/Cleveland_JASA_1979.pdf
//
// Original RATFOR implementation (public domain, I assume):
// https://svn.r-project.org/R/trunk/src/library/stats/src/lowess.doc
//
// Calling convention: `fitted_points = lowess(points, f, iter, delta);`, where
// `points` is an `Array` of objects. Each object has `x` and `y` Number values.
// The output is another `Array` of points.

var lowess; // the function we're defining

(function() {
  function square(x) { return x * x; }
  function cube(x) { return x * x * x; }

  function ratfor_lowest(x, y, n, xs, nleft, nright, w, userw, rw) { // returns ys, or null for ok=false
    var range = x[n - 1] - x[0];
    var h = Math.max(xs - x[nleft - 1], x[nright - 1] - xs);
    var h9 = 0.999 * h;
    var h1 = 0.001 * h;
    var a = 0.0; // sum of weights
    var ys; // output
    var j, r, nrt, b, c;

    // Compute weights (pick up all ties on right)
    for (j = nleft - 1; j < n; j += 1) {
      w[j] = 0;
      r = Math.abs(x[j] - xs);
      if (r <= h9) {
        // Small enough for non-zero weight
        if (r > h1) w[j] = cube(1.0 - cube(r / h));
        else        w[j] = 1;

        if (userw) w[j] *= rw[j];

        a += w[j];
      } else if (x[j] > xs) {
        break; // get out at first zero wt on right
      }
    }

    nrt = j - 1; // right most pt (may be greater than nright because of ties)

    if (a <= 0) {
      ys = null;
    } else {
      // weighted least squares
      for (j = nleft - 1; j <= nrt; j++) {
        w[j] /= a; // make sum of w(j) == 1
      }

      if (h > 0) {
        // use linear fit
        a = 0;
        for (j = nleft - 1; j <= nrt; j++) {
          a += w[j] * x[j]; // weighted center of x values
        }

        b = xs - a;
        c = 0;
        for (j = nleft - 1; j <= nrt; j++) {
          c += w[j] * square(x[j] - a);
        }

        if (c > square(.001 * range)) { // Obvious optimization, right?
          // points are spread out enough to compute slope
          b /= c;
          for (j = nleft - 1; j <= nrt; j++) {
            w[j] *= 1 + b * (x[j] - a);
          }
        }
      }

      ys = 0;
      for (j = nleft - 1; j <= nrt; j++) {
        ys += w[j] * y[j];
      }
    }

    return ys; // null or Number
  }

  function ratfor_lowess(x, y, n, f, nsteps, delta, ys, rw, res) {
    if (n < 2) {
      ys[0] = y[0];
      return;
    }

    var ns = Math.max(2, Math.min(n, Math.floor(f * n + 1e-7))); // at least two, at most n points
    var iter, nleft, nright, last, i, d1, d2, denom, j, alpha, cut, m1, m2, cmad, c9, c1, r;

    for (iter = 1; iter <= nsteps + 1; iter += 1) {
      nleft = 1;
      nright = ns;
      last = 0; // index of prev estimated point
      i = 1; // index of current point
      // beware: these indexes are 1, because Fortran. But Arrays are base 0.

      do {
        while (nright < n) {
          // move nleft, nright to right if radius decreases
          d1 = x[i - 1] - x[nleft - 1];
          d2 = x[nright] - x[i - 1];

          // If d1<=d2 with x(nright+1)==x(nright), lowest fixes
          if (d1 <= d2) break;

          // radius will not decrease by move right
          nleft += 1;
          nright += 1;
        }

        // fitted value at x(i)
        ys[i - 1] = ratfor_lowest(x, y, n, x[i - 1], nleft, nright, res, iter > 1, rw);
        if (ys[i - 1] === null) ys[i - 1] = y[i - 1];

        // all weights zero - copy over value (all rw==0)
        if (last < i - 1) {
          // skipped points -- interpolate
          denom = x[i - 1] - x[last - 1]; // non-zero - proof?
          for (j = last + 1; j < i; j += 1) {
            alpha = (x[j - 1] - x[last - 1]) / denom;
            ys[j - 1] = alpha * ys[i - 1] + (1 - alpha) * ys[last - 1];
          }
        }

        last = i; // last point actually estimated
        cut = x[last - 1] + delta; // x coord of close points

        for (i = last + 1; i <= n; i += 1) {
          // find close points
          if (x[i - 1] > cut) break; // i one beyond last pt within cut
          if (x[i - 1] == x[last - 1]) {
            // exact match in x
            ys[i - 1] = ys[last - 1];
            last = i;
          }
        }

        // back 1 point so interpolation within delta, but always go forward
        i = Math.max(last + 1, i - 1);
      } while (last < n);

      for (i = 0; i < n; i++) {
        res[i] = y[i] - ys[i];
      }

      if (iter > nsteps) break; // compute robustness weights except last time

      for (i = 0; i < n; i++) {
        rw[i] = Math.abs(res[i]);
      }

      rw.sort(function(a, b) { return a - b; });

      m1 = Math.floor(n / 2);
      m2 = n - m1 - 1;
      cmad = 3 * (rw[m1] + rw[m2]); // 6 median abs resid
      c9 = 0.999 * cmad;
      c1 = 0.111 * cmad;

      for (i = 0; i < n; i++) {
        r = Math.abs(res[i]);
        if (r <= c1) rw[i] = 1; // near 0, avoid underflow
        else if (r > c9) rw[i] = 0; // near 1, avoid underflow
        else rw[i] = square(1 - square(r / cmad));
      }
    }
  }

  lowess = function _lowess(points, f, iter, delta) {
    var sorted_points = points.slice().sort(function(p1, p2) { return p1.x - p2.x || p1.y - p2.y; });
    var x = sorted_points.map(function(p) { return p.x; });
    var y = sorted_points.map(function(p) { return p.y; });
    var n = points.length;
    var ys = new Array(n);
    var rw = new Array(n);
    var res = new Array(n);

    ratfor_lowess(x, y, n, f, iter, delta, ys, rw, res);

    return sorted_points.map(function(pt, i) { return { x: pt.x, y: ys[i] }; });
  };

  lowess._ratfor_lowess = ratfor_lowess;
})();
