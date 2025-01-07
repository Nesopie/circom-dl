const { assert, log } = require("console");
const path = require("path");
const Scalar = require("ffjavascript").Scalar;
const wasm_tester = require("circom_tester").wasm;

function bigintToArray(n, k, x) {
  let mod = BigInt(1);
  for (let idx = 0; idx < n; idx++) {
    mod *= BigInt(2);
  }

  const ret = [];
  let xTemp = x;
  for (let idx = 0; idx < k; idx++) {
    ret.push(xTemp % mod);
    xTemp /= mod;
  }

  return ret;
}

function modInverse(a, m) {
  a = BigInt(a);
  m = BigInt(m);

  let m0 = m;
  let x0 = BigInt(0);
  let x1 = BigInt(1);

  if (m === 1n) return 0n;

  while (a > 1n) {
    let q = a / m;
    let t = m;

    m = a % m;
    a = t;
    t = x0;

    x0 = x1 - q * x0;
    x1 = t;
  }

  if (x1 < 0n) {
    x1 += m0;
  }

  return x1;
}

function point_double(x1, y1, a, p) {
  x1 = BigInt(x1);
  y1 = BigInt(y1);
  a = BigInt(a);
  p = BigInt(p);

  if (y1 === 0n) {
    return { x: null, y: null };
  }

  let lambda_num = (3n * x1 * x1 + a) % p;
  let lambda_den = modInverse(2n * y1, p);
  let lam = (lambda_num * lambda_den) % p;

  let x3 = (lam * lam - 2n * x1) % p;
  let y3 = (lam * (x1 - x3) - y1) % p;

  if (x3 < 0n) x3 += p;
  if (y3 < 0n) y3 += p;

  return { x: x3, y: y3 };
}

function point_add(x1, y1, x2, y2, p) {
  x1 = BigInt(x1);
  y1 = BigInt(y1);
  x2 = BigInt(x2);
  y2 = BigInt(y2);
  p = BigInt(p);

  if (x1 === x2 && y1 === y2) {
    throw new Error("Points are the same; use point_double instead.");
  }

  if (x1 === x2) {
    return { x: null, y: null };
  }
  let lambda_num = (p + y2 - y1) % p;
  let lambda_den = modInverse((p + x2 - x1) % p, p);
  let lam = (lambda_num * lambda_den) % p;

  let x3 = (2n * p + lam * lam - x1 - x2) % p;
  let y3 = (p + lam * (x1 - x3) - y1) % p;

  if (x3 < 0n) x3 += p;
  if (y3 < 0n) y3 += p;

  return { x: x3, y: y3 };
}

function point_scalar_mul(x, y, k, a, p) {
  let x_res = null;
  let y_res = null;

  let x_cur = x;
  let y_cur = y;

  while (k > 0n) {
    if (k & 1n) {
      if (x_res === null && y_res === null) {
        x_res = x_cur;
        y_res = y_cur;
      } else {
        const { x: x_temp, y: y_temp } = point_add(
          x_res,
          y_res,
          x_cur,
          y_cur,
          p
        );
        x_res = x_temp;
        y_res = y_temp;
      }
    }

    const { x: x_temp, y: y_temp } = point_double(x_cur, y_cur, a, p);
    x_cur = x_temp;
    y_cur = y_temp;

    k >>= 1n; // Shift k right by 1 bit
  }

  return { x: x_res, y: y_res };
}

function bit_arr_to_num(arr) {
  res = 0n;
  for (var i = 0; i < arr.length; i++) {
    res += BigInt(arr[i]) * 2n ** (BigInt(arr.length) - 1n - BigInt(i));
  }
  return res;
}

async function testVerBits(input1, input2, input3, input4, input5, circuit) {
  let input = [
    [bigintToArray(64, 6, input1), bigintToArray(64, 6, input2)],
    [bigintToArray(64, 6, input3), bigintToArray(64, 6, input4)],
    input5,
  ];

  let n =
    0x8cb91e82a3386d280f5d6f7e50e641df152f7109ed5456b31f166e6cac0425a7cf3ab6af6b7fc3103b883202e9046565n;
  let hn = BigInt(bit_arr_to_num(input5));
  let sinv = modInverse(input4, n);
  let sh = (sinv * hn) % n;
  let sr = (sinv * input3) % n;
  let p1 = point_scalar_mul(
    input1,
    input2,
    sr,
    0x7bc382c63d8c150c3c72080ace05afa0c2bea28e4fb22787139165efba91f90f8aa5814a503ad4eb04a8c7dd22ce2826n,
    0x8cb91e82a3386d280f5d6f7e50e641df152f7109ed5456b412b1da197fb71123acd3a729901d1a71874700133107ec53n
  );
  let p2 = point_scalar_mul(
    0x1d1c64f068cf45ffa2a63a81b7c13f6b8847a3e77ef14fe3db7fcafe0cbd10e8e826e03436d646aaef87b2e247d4af1en,
    0x8abe1d7520f9c2a45cb1eb8e95cfd55262b70b29feec5864e19c054ff99129280e4646217791811142820341263c5315n,
    sh,
    0x7bc382c63d8c150c3c72080ace05afa0c2bea28e4fb22787139165efba91f90f8aa5814a503ad4eb04a8c7dd22ce2826n,
    0x8cb91e82a3386d280f5d6f7e50e641df152f7109ed5456b412b1da197fb71123acd3a729901d1a71874700133107ec53n
  );

  let p3 = point_add(
    p1.x,
    p1.y,
    p2.x,
    p2.y,
    0x8cb91e82a3386d280f5d6f7e50e641df152f7109ed5456b412b1da197fb71123acd3a729901d1a71874700133107ec53n
  );

  let real_result = p3.x == input3;
  console.log(real_result);
  console.log(
    JSON.stringify({
      pubkey: input[0],
      signature: input[1],
      hashed: input[2],
      dummy: 0n,
    })
  );

  // try {
  //   const w = await circuit.calculateWitness(
  //     { pubkey: input[0], signature: input[1], hashed: input[2], dummy: 0n },
  //     true
  //   );

  //   if (!real_result) {
  //     throw new Error(
  //       `Expected failure for verification (${input1}, ${input2}), (${input3}, ${input4}) ${input5}, but it passed.`
  //     );
  //   }
  // } catch (err) {
  //   if (real_result) {
  //     throw new Error(
  //       `Unexpected failure for verification (${input1}, ${input2}), (${input3}, ${input4}) ${input5}.`
  //     );
  //   } else {
  //     console.log(
  //       `Predicted failure for verification (${input1}, ${input2}), (${input3}, ${input4}) ${input5} not on curve correctly handled.`
  //     );
  //   }
  // }
}

// describe("Ecdsa num test", function () {

//     this.timeout(10000000);
//     let circuit;

//     before(async () => {
//         circuit = await wasm_tester(path.join(__dirname, "circuits", "signatures", "ecdsaNum.circom"));
//     });

//     it("Ver correct signature", async function () {
//         await testVerNum(31374990377422060663897166666788812921270243020104798068084951911347116539007n, 41157152733927076370846415947227885284998856909034587685323725392788996793783n, 41785691604214669431201278410214784582546070760560366208613932232380633581249n, 45015635295556179986733632766516885633143292479837071894657301025399130399180n, 53877815096637157910110176920073475792177340572623780182175655462294595163782n, circuit);
//     });

//     it("Ver incorrect signature, should handle failture", async function () {
//         await testVerNum(31374990377422060663897166666788812921270243020104798068084951911347116539007n, 41157152733927076370846415947227885284998856909034587685323725392788996793783n, 41785691604214669431201278410214784582546070760560366208613932232380633581249n, 45015635295556179986733632766516885633143292479837071894657301025399130399180n, 53877815096637157910110176920073475792177340572623780182175655462294595163783n, circuit);
//     });
// });

describe("Ecdsa bits test", function () {
  this.timeout(10000000);
  let circuit;

  // before(async () => {
  //   circuit = await wasm_tester(
  //     path.join(__dirname, "circuits", "signatures", "ecdsaBits.circom")
  //   );
  // });

  it("Ver correct signature", async function () {
    await testVerBits(
      0x7f4a7660ddcbaeee6267c2918597d4b61bf005af6e49982c2a599e044edea7376926f9062f74121ced86885ecdbfc318n,
      0x11eaeaa70cb29e500bf582bc1c0a805cea0e6beacf46f1be9855d16324594ccc081f9fd42c8dbd1feb4baac45e8f1e31n,
      0x3a0b01935621e2b7719542457629bc008502ed43810312dd34ab33b700eca17bd9d4a34bf4201778c286f373fb73ef6dn,
      0x7b1103d1289266de9a148bcab14a50af6374ab9c1031db3f6f6eba564fcbc2eca1aa272ec587653696ee031afd33fa63n,
      [
        1n,
        1n,
        0n,
        0n,
        0n,
        0n,
        0n,
        1n,
        1n,
        1n,
        0n,
        0n,
        0n,
        1n,
        0n,
        1n,
        0n,
        1n,
        1n,
        1n,
        0n,
        1n,
        1n,
        0n,
        0n,
        1n,
        1n,
        0n,
        0n,
        1n,
        0n,
        1n,
        1n,
        1n,
        1n,
        0n,
        0n,
        0n,
        0n,
        0n,
        0n,
        0n,
        0n,
        1n,
        1n,
        1n,
        1n,
        1n,
        0n,
        1n,
        0n,
        1n,
        1n,
        0n,
        1n,
        1n,
        1n,
        0n,
        0n,
        1n,
        1n,
        1n,
        1n,
        1n,
        0n,
        0n,
        1n,
        0n,
        1n,
        0n,
        0n,
        0n,
        0n,
        1n,
        1n,
        1n,
        1n,
        0n,
        1n,
        0n,
        1n,
        0n,
        1n,
        1n,
        1n,
        1n,
        0n,
        1n,
        0n,
        0n,
        0n,
        0n,
        0n,
        1n,
        1n,
        0n,
        1n,
        0n,
        1n,
        1n,
        1n,
        0n,
        1n,
        1n,
        0n,
        0n,
        0n,
        0n,
        0n,
        1n,
        0n,
        0n,
        0n,
        0n,
        0n,
        1n,
        1n,
        0n,
        1n,
        0n,
        1n,
        1n,
        0n,
        1n,
        1n,
        1n,
        1n,
        0n,
        0n,
        1n,
        1n,
        1n,
        1n,
        0n,
        0n,
        0n,
        1n,
        1n,
        1n,
        1n,
        0n,
        0n,
        1n,
        0n,
        0n,
        1n,
        1n,
        0n,
        0n,
        1n,
        1n,
        0n,
        0n,
        0n,
        1n,
        0n,
        0n,
        1n,
        1n,
        1n,
        1n,
        0n,
        0n,
        1n,
        1n,
        1n,
        0n,
        0n,
        0n,
        0n,
        1n,
        0n,
        1n,
        0n,
        1n,
        0n,
        1n,
        1n,
        0n,
        1n,
        1n,
        0n,
        1n,
        0n,
        1n,
        0n,
        1n,
        0n,
        0n,
        1n,
        0n,
        0n,
        1n,
        0n,
        1n,
        1n,
        0n,
        1n,
        1n,
        1n,
        1n,
        0n,
        1n,
        0n,
        1n,
        1n,
        1n,
        1n,
        0n,
        0n,
        1n,
        1n,
        1n,
        1n,
        0n,
        1n,
        1n,
        0n,
        1n,
        1n,
        0n,
        0n,
        0n,
        0n,
        0n,
        0n,
        1n,
        1n,
        1n,
        1n,
        1n,
        1n,
        1n,
        0n,
        1n,
        0n,
        1n,
        0n,
        0n,
        1n,
        0n,
        1n,
        0n,
        1n,
        0n,
        1n,
        1n,
        0n,
        1n,
        0n,
        0n,
        1n,
        1n,
        0n,
        0n,
        1n,
        0n,
        0n,
        1n,
        0n,
        0n,
        1n,
        1n,
        1n,
        1n,
        0n,
        1n,
        1n,
        1n,
        1n,
        1n,
        1n,
        1n,
        1n,
        0n,
        1n,
        1n,
        1n,
        1n,
        1n,
        1n,
        1n,
        1n,
        1n,
        1n,
        1n,
        1n,
        1n,
        1n,
        1n,
        1n,
        1n,
        1n,
        0n,
        0n,
        1n,
        1n,
        1n,
        0n,
        1n,
        1n,
        0n,
        0n,
        1n,
        0n,
        1n,
        1n,
        1n,
        0n,
        0n,
        0n,
        1n,
        1n,
        1n,
        0n,
        1n,
        0n,
        0n,
        1n,
        1n,
        1n,
        0n,
        0n,
        0n,
        0n,
        1n,
        1n,
        1n,
        1n,
        1n,
        0n,
        0n,
        1n,
        1n,
        1n,
        1n,
        0n,
        1n,
        1n,
        0n,
        0n,
        0n,
        1n,
        1n,
        0n,
        1n,
        0n,
        0n,
        1n,
        0n,
        0n,
        0n,
        1n,
        1n,
        1n,
        1n,
        0n,
        0n,
        1n,
        1n,
        0n,
        1n,
        0n,
        1n,
        1n,
        0n,
        1n,
        0n,
        1n,
        0n,
        0n,
        1n,
        1n,
        0n,
        1n,
        1n,
        0n,
        0n,
        0n,
        0n,
        1n,
        1n,
        1n,
        1n,
      ],
      circuit
    );
  });

  //   it("Ver incorrect signature, should handle failture", async function () {
  //     await testVerBits(
  //       31374990377422060663897166666788812921270243020104798068084951911347116539007n,
  //       41157152733927076370846415947227885284998856909034587685323725392788996793783n,
  //       41785691604214669431201278410214784582546070760560366208613932232380633581249n,
  //       45015635295556179986733632766516885633143292479837071894657301025399130399180n,
  //       [
  //         0n,
  //         1n,
  //         1n,
  //         1n,
  //         0n,
  //         1n,
  //         1n,
  //         1n,
  //         0n,
  //         0n,
  //         0n,
  //         1n,
  //         1n,
  //         1n,
  //         0n,
  //         1n,
  //         1n,
  //         1n,
  //         0n,
  //         0n,
  //         0n,
  //         0n,
  //         1n,
  //         1n,
  //         0n,
  //         0n,
  //         1n,
  //         1n,
  //         1n,
  //         1n,
  //         1n,
  //         1n,
  //         0n,
  //         1n,
  //         1n,
  //         0n,
  //         1n,
  //         0n,
  //         1n,
  //         1n,
  //         1n,
  //         0n,
  //         1n,
  //         0n,
  //         0n,
  //         0n,
  //         1n,
  //         1n,
  //         0n,
  //         1n,
  //         0n,
  //         1n,
  //         1n,
  //         1n,
  //         0n,
  //         1n,
  //         1n,
  //         1n,
  //         0n,
  //         1n,
  //         1n,
  //         1n,
  //         0n,
  //         1n,
  //         1n,
  //         1n,
  //         1n,
  //         1n,
  //         0n,
  //         0n,
  //         1n,
  //         1n,
  //         1n,
  //         0n,
  //         1n,
  //         0n,
  //         0n,
  //         0n,
  //         0n,
  //         1n,
  //         0n,
  //         0n,
  //         0n,
  //         1n,
  //         0n,
  //         1n,
  //         1n,
  //         0n,
  //         0n,
  //         0n,
  //         0n,
  //         1n,
  //         0n,
  //         0n,
  //         1n,
  //         1n,
  //         1n,
  //         0n,
  //         0n,
  //         1n,
  //         0n,
  //         1n,
  //         0n,
  //         0n,
  //         0n,
  //         0n,
  //         0n,
  //         0n,
  //         1n,
  //         0n,
  //         1n,
  //         0n,
  //         0n,
  //         0n,
  //         1n,
  //         0n,
  //         1n,
  //         0n,
  //         1n,
  //         0n,
  //         1n,
  //         1n,
  //         0n,
  //         1n,
  //         1n,
  //         1n,
  //         0n,
  //         1n,
  //         0n,
  //         0n,
  //         0n,
  //         0n,
  //         0n,
  //         0n,
  //         1n,
  //         1n,
  //         1n,
  //         0n,
  //         0n,
  //         0n,
  //         1n,
  //         0n,
  //         1n,
  //         1n,
  //         1n,
  //         1n,
  //         1n,
  //         1n,
  //         1n,
  //         0n,
  //         1n,
  //         0n,
  //         1n,
  //         0n,
  //         0n,
  //         0n,
  //         1n,
  //         0n,
  //         0n,
  //         1n,
  //         1n,
  //         1n,
  //         0n,
  //         0n,
  //         1n,
  //         0n,
  //         1n,
  //         0n,
  //         0n,
  //         1n,
  //         0n,
  //         0n,
  //         0n,
  //         1n,
  //         1n,
  //         1n,
  //         1n,
  //         1n,
  //         1n,
  //         1n,
  //         0n,
  //         0n,
  //         1n,
  //         1n,
  //         1n,
  //         0n,
  //         1n,
  //         0n,
  //         0n,
  //         1n,
  //         1n,
  //         1n,
  //         0n,
  //         0n,
  //         0n,
  //         1n,
  //         0n,
  //         1n,
  //         1n,
  //         1n,
  //         0n,
  //         0n,
  //         1n,
  //         1n,
  //         0n,
  //         1n,
  //         1n,
  //         0n,
  //         0n,
  //         1n,
  //         0n,
  //         1n,
  //         0n,
  //         1n,
  //         0n,
  //         1n,
  //         1n,
  //         1n,
  //         1n,
  //         1n,
  //         0n,
  //         1n,
  //         0n,
  //         1n,
  //         1n,
  //         1n,
  //         0n,
  //         0n,
  //         1n,
  //         0n,
  //         0n,
  //         0n,
  //         0n,
  //         0n,
  //         0n,
  //         1n,
  //         1n,
  //         1n,
  //         0n,
  //         1n,
  //         1n,
  //         1n,
  //         0n,
  //         1n,
  //         0n,
  //         1n,
  //         1n,
  //         0n,
  //         1n,
  //         0n,
  //         0n,
  //         0n,
  //         0n,
  //         1n,
  //         1n,
  //         1n,
  //       ],
  //       circuit
  //     );
  //   });
});
