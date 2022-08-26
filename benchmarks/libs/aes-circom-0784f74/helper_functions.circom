// Copyright © 2022, Electron Labs
pragma circom 2.0.0;

include "../circomlib-cff5ab6/bitify.circom";
include "../circomlib-cff5ab6/gates.circom";
include "../circomlib-cff5ab6/comparators.circom";

template BitwiseRightShift(n, r) {
    signal input in[n];
    signal output out[n];

    for(var i=0; i<n; i++){
        if(i+r>=n){
            out[i] <== 0;
        } else {
            out[i] <== in[i+r];
        }
    }
}

template IntRightShift(n, x)
{	
    signal input in;
    signal output out;
    
    component num2bits = Num2Bits(n);
    num2bits.in <== in;

    component bits2num = Bits2Num(n);
    var i;
    for(i=0; i<n; i++)
    {
        if(i+x<n) bits2num.in[i] <== num2bits.out[i+x];
        else bits2num.in[i] <== 0;
    } 
    out <== bits2num.out;
}

template BitwiseLeftShift(n, r) {
    signal input in[n];
    signal output out[n];
    var j=0;
    for (var i=0; i<n; i++) {
        if (i < r) {
            out[i] <== 0;
        } else {
            out[i] <== in[j];
            j++;
        }
    }
}

template IntLeftShift(n, x)
{	
    signal input in;
    signal output out;
    
    component num2bits = Num2Bits(n);
    num2bits.in <== in;

    component bits2num = Bits2Num(n);
    for(var i=0; i<n; i++)
    {
        if(i<x) bits2num.in[i] <== 0;
        else bits2num.in[i] <== num2bits.out[i-x];
    }
    out <== bits2num.out;
}

template BitwiseXor(n) {
    signal input a[n];
    signal input b[n];
    signal output out[n];
    signal mid[n];

    for (var k=0; k<n; k++) {
        mid[k] <== a[k]*b[k];
        out[k] <== a[k] + b[k] - 2*mid[k];
    }
}

template IntXor(n)
{
    signal input a;
    signal input b;

    signal output out;

    component num2bits[2];
    num2bits[0] = Num2Bits(n);
    num2bits[1] = Num2Bits(n);

    num2bits[0].in <== a;
    num2bits[1].in <== b;
    
    component xor[n];
    for(var i=0; i<n; i++) xor[i] = XOR();

    component bits2num = Bits2Num(n);
    for(var i=0; i<n; i++)
    {
        xor[i].a <== num2bits[0].out[i];
        xor[i].b <== num2bits[1].out[i];

        bits2num.in[i] <== xor[i].out;
    }

    out <== bits2num.out;
}

template BitwiseAnd(n) {
    signal input a[n];
    signal input b[n];
    signal output out[n];

    for (var k=0; k<n; k++) {
        out[k] <== a[k]*b[k];
    }
}

template IntAnd(n)
{
    signal input a;
    signal input b;

    signal output out;

    component num2bits[2];
    num2bits[0] = Num2Bits(n);
    num2bits[1] = Num2Bits(n);

    num2bits[0].in <== a;
    num2bits[1].in <== b;
    component and[n];
    for(var i=0; i<n; i++) and[i] = AND();

    component bits2num = Bits2Num(n);
    for(var i=0; i<n; i++)
    {
        and[i].a <== num2bits[0].out[i];
        and[i].b <== num2bits[1].out[i];
        bits2num.in[i] <== and[i].out;
    }

    out <== bits2num.out;
}

template IntOr(n)
{
    signal input a;
    signal input b;

    signal output out;

    component num2bits[2];
    num2bits[0] = Num2Bits(n);
    num2bits[1] = Num2Bits(n);

    num2bits[0].in <== a;
    num2bits[1].in <== b;
    component or[n];
    for(var i=0; i<n; i++) or[i] = OR();

    component bits2num = Bits2Num(n);
    for(var i=0; i<n; i++)
    {
        or[i].a <== num2bits[0].out[i];
        or[i].b <== num2bits[1].out[i];
        bits2num.in[i] <== or[i].out;
    }

    out <== bits2num.out;
}

template Typecast(in_size, in_bits, out_bits)
{

    var out_size = (in_size*in_bits)/out_bits;
    signal input in[in_size];
    signal output out[out_size];

    var i, j, k;

    component num2bits[in_size];
    for(i=0; i<in_size; i++) num2bits[i] = Num2Bits(in_bits);

    component bits2num[out_size];
    for(i=0; i<out_size; i++) bits2num[i] = Bits2Num(out_bits);

    if(in_bits > out_bits)
    {
        var ratio = in_bits/out_bits;
        for(i=0; i<in_size; i++)
        {
            num2bits[i].in <== in[i];
            for(j=0; j<ratio; j++){
                var index = i*ratio + j;
                for(k=0; k<out_bits; k++) bits2num[index].in[k] <== num2bits[i].out[j*out_bits+k];
                out[index] <== bits2num[index].out;
            }
        }
    }
    else if(out_bits > in_bits)
    {
        var ratio = out_bits/in_bits;
        for(i=0; i<out_size; i++)
        {
            for(j=0; j<ratio; j++)
            {
                var index = i*ratio + j;
                num2bits[index].in <== in[index];
                for(k=0; k<in_bits; k++) bits2num[i].in[j*in_bits+k] <== num2bits[index].out[k];
            }
            out[i] <== bits2num[i].out;
        }
    }
}

template SumMultiple(n) {
    signal input nums[n];
    signal output sum;

    signal sums[n];
    sums[0] <== nums[0];

    for(var i=1; i<n; i++) {
        sums[i] <== sums[i-1] + nums[i];
    }

    sum <== sums[n-1];
}

template IndexSelector(total) {
    signal input in[total];
    signal input index;
    signal output out;

    //maybe add (index<total) check later when we decide number of bits

    component calcTotal = SumMultiple(total);
    component equality[total];

    for(var i=0; i<total; i++){
        equality[i] = IsEqual();
        equality[i].in[0] <== i;
        equality[i].in[1] <== index;
        calcTotal.nums[i] <== equality[i].out * in[i];
    }

    out <== calcTotal.sum;
}
