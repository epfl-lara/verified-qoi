import stainless.*
import stainless.lang.{ghost as ghostExpr, inline as inlineCall, *}
import stainless.collection.*
import stainless.annotation.{inlineOnce, mutable, opaque, pure, ghost as ghostDef}
import stainless.proof.*
import common.*
import decoder.{decodeBigStepProp, decodeRangePureLemma, decodeRangePureBytesEqLemma,
  decodeRangePureMergedLemma}

object encoder {

  case class Ctx(pixels: Array[Byte], w: Long, h: Long, chan: Long) {
    require(w > 0 && h > 0 && w < 8192 && h < 8192 &&
      3 <= chan && chan <= 4 &&
      w * h * chan == pixels.length)

    @inline
    def maxSize: Long = w * h * (chan + 1) + HeaderSize + Padding

    @inline
    def pxEnd: Long = pixels.length - chan
  }

  case class RunUpdate(reset: Boolean, run: Long, outPos: Long)

  case class LoopIter(px: Int, pxPrev: Int, pxPos: Long)

  /////////////////////////////////////////////////////////////////////////////////////////////////////

  def positionsIneqInv(run: Long, outPos: Long, pxPos: Long)(using Ctx): Boolean =
    chan * (outPos - HeaderSize + chan * run) <= (chan + 1) * pxPos

  def runInv(run: Long): Boolean =
    0 <= run && run < 62

  def pxPosInv(pxPos: Long)(using Ctx): Boolean =
    0 <= pxPos && pxPos <= pixels.length && pxPos % chan == 0

  def outPosInv(outPos: Long)(using Ctx): Boolean =
    HeaderSize <= outPos && outPos <= maxSize - Padding

  def rangesInv(run: Long, outPos: Long, pxPos: Long)(using Ctx): Boolean =
    pxPosInv(pxPos) && runInv(run) && outPosInv(outPos)

  def rangesInv(indexLen: Long, bytesLen: Long, run: Long, outPos: Long, pxPos: Long)(using Ctx): Boolean =
    pxPosInv(pxPos) && runInv(run) && outPosInv(outPos) && bytesLen == maxSize && indexLen == 64

  @opaque
  @inlineOnce
  def withinBoundsLemma(run: Long, outPos: Long, pxPos: Long)(using Ctx): Unit = {
    require(rangesInv(run, outPos, pxPos))
    require(positionsIneqInv(run, outPos, pxPos))
    require(pxPos + chan <= pixels.length)
    assert(chan * (outPos - HeaderSize + chan * run + chan + 1) <= (chan + 1) * (pxPos + chan))
    assert(chan * (outPos - HeaderSize + chan * run + chan + 1) <= (chan + 1) * pixels.length)
    assert(pixels.length * (chan + 1) == w * h * chan * (chan + 1))
    assert(chan * (maxSize - HeaderSize - Padding) == w * h * chan * (chan + 1))
    assert((chan + 1) * pixels.length == chan * (maxSize - HeaderSize - Padding))
    assert(chan * (outPos - HeaderSize + chan * run + chan + 1) <= chan * (maxSize - HeaderSize - Padding))
    assert(outPos - HeaderSize + chan * run + chan + 1 <= maxSize - HeaderSize - Padding) // ~23s
  }.ensuring(_ => outPos + run * chan + chan + 1 + Padding <= maxSize)

  @opaque
  @inlineOnce
  def withinBoundsLemma2(run: Long, outPos: Long, pxPos: Long)(using Ctx): Unit = {
    require(rangesInv(run, outPos, pxPos))
    require(positionsIneqInv(run, outPos, pxPos))
    assert(chan * (outPos - HeaderSize + chan * run + chan + 1) <= (chan + 1) * (pxPos + chan))
    assert(chan * (outPos - HeaderSize + chan * run + chan + 1) <= (chan + 1) * (pixels.length + chan))
    assert(pixels.length * (chan + 1) == w * h * chan * (chan + 1))
    assert(chan * (maxSize - HeaderSize - Padding) == w * h * chan * (chan + 1))
    assert((chan + 1) * pixels.length == chan * (maxSize - HeaderSize - Padding))

    assert(chan * (outPos - HeaderSize + chan * run + chan + 1) - (chan + 1) * chan <= (chan + 1) * (pixels.length + chan) - (chan + 1) * chan)
    assert(chan * (outPos - HeaderSize + chan * run) <= (chan + 1) * pixels.length)
    assert(chan * (outPos - HeaderSize + chan * run) <= chan * (maxSize - HeaderSize - Padding))
    assert(outPos - HeaderSize + chan * run <= maxSize - HeaderSize - Padding)
    assert(outPos + chan * run + Padding <= maxSize)
  }.ensuring(_ => outPos + chan * run + Padding <= maxSize)

  @opaque
  @inlineOnce
  def positionsIneqIncrementedLemma(run: Long, outPos: Long, pxPos: Long)(using Ctx): Unit = {
    require(rangesInv(run, outPos, pxPos))
    require(positionsIneqInv(run, outPos, pxPos))
  }.ensuring(_ => positionsIneqInv(run, outPos + chan + 1, pxPos + chan))

  @opaque
  @inlineOnce
  def loopInvUpperOutPosLemma(run: Long, oldOutPos: Long, pxPos: Long, newOutPos: Long)(using Ctx): Unit = {
    require(rangesInv(run, oldOutPos, pxPos))
    require(HeaderSize <= newOutPos && newOutPos <= oldOutPos + chan + 1)
    require(positionsIneqInv(run, oldOutPos + chan + 1, pxPos))
    assert(chan * ((oldOutPos - HeaderSize) + chan * run) <= (chan + 1) * pxPos)
    assert(chan * (newOutPos - HeaderSize) <= chan * (oldOutPos + chan + 1 - HeaderSize))
    assert(chan * ((newOutPos - HeaderSize) + chan * run) <= chan * ((oldOutPos + chan + 1 - HeaderSize) + chan * run))
  }.ensuring(_ => positionsIneqInv(run, newOutPos, pxPos))

  /////////////////////////////////////////////////////////////////////////////////////////////////////

  case class Decoded(var index: Array[Int],
                     var pixels: Array[Byte],
                     var inPos: Long,
                     var pxPos: Long)

  def encode(using Ctx): Unit = {
    val bytes = Array.fill(maxSize.toInt)(0: Byte)
    val index = Array.fill(64)(0)
    write32(bytes, 0, MagicNumber)
    write16(bytes, 4, w.toShort)
    write16(bytes, 6, h.toShort)
    write32(bytes, 8, 0)
    val pxPrev = Pixel.fromRgba(0, 0, 0, 255.toByte)
    val decoded = Decoded(freshCopy(index), Array.fill(pixels.length)(0: Byte), HeaderSize, 0)
    val oldDecoded = freshCopy(decoded)
    val (pxRes, outPos) = encodeLoop(index, bytes, pxPrev, 0, HeaderSize, 0, decoded)

    assert(decodeEncodeProp(bytes, pxPrev, HeaderSize, outPos, oldDecoded, pxRes, decoded))

//    // TODO: No longer necessary with new format
//    val dataLen = outPos + Padding - HeaderSize
//    write32(bytes, 8, dataLen.toInt)
  }

  def encodeLoop(index: Array[Int], bytes: Array[Byte], pxPrev: Int, run0: Long, outPos0: Long, pxPos: Long, decoded: Decoded)(using Ctx): (Int, Long) = {
    decreases(pixels.length - pxPos)
    require(rangesInv(index.length, bytes.length, run0, outPos0, pxPos))
    require(pxPos < pixels.length && pxPos + chan <= pixels.length)
    require(positionsIneqInv(run0, outPos0, pxPos))
    require((chan == 3) ==> (Pixel.a(pxPrev) == 255.toByte))
    require(decoded.inPos == outPos0)
    require(decoded.index == index)
    require(decoded.pixels.length == pixels.length)
    require(0 <= decoded.pxPos && decoded.pxPos < decoded.pixels.length)
    require(decoded.pxPos + chan <= decoded.pixels.length)
    require(decoded.pxPos % chan == 0)
    require(decoded.pxPos <= pxPos && decoded.pxPos + chan * run0 == pxPos)
    require(arraysEq(decoded.pixels, pixels, 0, decoded.pxPos))
    require((run0 > 0) ==> samePixelsForall(pixels, pxPrev, decoded.pxPos, pxPos, chan))

    val oldDecoded = freshCopy(decoded)
    val oldBytes = freshCopy(bytes)
    val (px, outPos2, run1) = encodeSingleStep(index, bytes, pxPrev, run0, outPos0, pxPos, decoded)
    assert(decoded.pixels.length == pixels.length)
    check(bytes.length == maxSize)
    check(oldBytes.length == bytes.length)
    check(index.length == 64)
    check(index == decoded.index)
    check(HeaderSize <= outPos2 && outPos2 <= maxSize - Padding)
    assert(rangesInv(index.length, bytes.length, run1, outPos2, pxPos))
    assert(positionsIneqInv(run1, outPos2, pxPos + chan))
    assert((chan == 3) ==> (Pixel.a(px) == 255.toByte))
    assert(decoded.inPos == outPos2)
    assert(samePixels(pixels, px, pxPos, chan))
    assert(decoded.index == index)
    assert(decoded.pxPos + chan * run1 == pxPos + chan)
    assert(decoded.pxPos % chan == 0)
    assert(0 <= decoded.pxPos)
    assert(arraysEq(oldBytes, bytes, 0, outPos0))
    assert((outPos0 < outPos2) ==> decodeEncodeProp(bytes, pxPrev, outPos0, outPos2, oldDecoded, px, decoded))

    if (pxPos + chan < pixels.length) {
      val pxPosPlusChan = pxPos + chan
      sorry(pxPosPlusChan % chan == 0) // TODO
      sorry(pxPosPlusChan + chan <= pixels.length) // TODO
      assert(rangesInv(index.length, bytes.length, run1, outPos2, pxPosPlusChan))

      if (outPos0 == outPos2) {
        assert(run1 == run0 + 1)
        assert(px == pxPrev)
        check(decoded == oldDecoded)

        check(decoded.pxPos + chan <= decoded.pixels.length)
        check(decoded.pxPos % chan == 0)

        check(decoded.pxPos < decoded.pixels.length)
        check(decoded.pxPos + chan <= decoded.pixels.length)
        check(arraysEq(decoded.pixels, pixels, 0, decoded.pxPos))

        samePixelsSingleElementRange(pixels, px, decoded.pxPos, chan)
        if (run0 != 0) {
          assert(samePixelsForall(pixels, pxPrev, decoded.pxPos, pxPos, chan)) // Precond 3 slow (~70s)
          samePixelsForallCombinedLemma(pixels, px, decoded.pxPos, pxPos, pxPosPlusChan, chan)
          check(samePixelsForall(pixels, pxPrev, decoded.pxPos, pxPosPlusChan, chan))
        } else {
          assert(decoded.pxPos == pxPos)
          check(samePixelsForall(pixels, pxPrev, decoded.pxPos, pxPosPlusChan, chan))
        }
        check((run1 > 0) ==> samePixelsForall(pixels, pxPrev, decoded.pxPos, pxPosPlusChan, chan))
      } else {
        assert(outPos0 < outPos2)
        assert(run1 == 0)
        assert(decoded.pxPos == pxPos + chan)
        assert(decodeEncodeProp(bytes, pxPrev, outPos0, outPos2, oldDecoded, px, decoded))

        check(decoded.pxPos < decoded.pixels.length)
        check(decoded.pxPos + chan <= decoded.pixels.length)

        assert(arraysEq(pixels, decoded.pixels, 0, decoded.pxPos))
        arraysEqSymLemma(pixels, decoded.pixels, 0, decoded.pxPos)
        check(arraysEq(decoded.pixels, pixels, 0, decoded.pxPos))
        check((run1 > 0) ==> samePixelsForall(pixels, pxPrev, decoded.pxPos, pxPosPlusChan, chan))
      }

      val bytesPreRec = freshCopy(bytes)
      val decodedPreRec = freshCopy(decoded)
      val (pxRes, outPosRes) = encodeLoop(index, bytes, px, run1, outPos2, pxPosPlusChan, decoded)
      check(bytes.length == maxSize && index == decoded.index)
      check(oldBytes.length == bytes.length)
      assert(index.length == 64 && decoded.index.length == 64)
      check(HeaderSize <= outPosRes && outPosRes <= maxSize - Padding)
      check(outPos0 < outPosRes)
      check(outPos2 < outPosRes)
      check(outPosRes <= bytes.length - Padding)
      assert(decodeEncodeProp(bytes, px, outPos2, outPosRes, decodedPreRec, pxRes, decoded))
      assert(arraysEq(bytesPreRec, bytes, 0, outPos2))

      // From encodeSingleStep, which holds for bytes and decoded prior to the recursive call
      // assert((outPos0 < outPos2) ==> decodeEncodeProp(bytesPreRec, pxPrev, pxPos, outPos0, outPos2, oldDecoded, decodedPreRec))

      if (outPos0 == outPos2) {
        sorry(decodeEncodeProp(bytes, pxPrev, outPos0, outPosRes, oldDecoded, px, decoded)) // TODO: limite limite
      } else {
        assert(outPos0 < outPos2)
        assert(decodeEncodeProp(bytesPreRec, pxPrev, outPos0, outPos2, oldDecoded, px, decodedPreRec))

        arraysEqDropLeftLemma(bytesPreRec, bytes, 0, outPos0, outPos2)
        assert(arraysEq(bytesPreRec, bytes, outPos0, outPos2))
        decodeEncodePropBytesEqLemma(bytesPreRec, bytes, pxPrev, pxPos, outPos0, outPos2, oldDecoded, px, decodedPreRec)
        assert(decodeEncodeProp(bytes, pxPrev, outPos0, outPos2, oldDecoded, px, decodedPreRec))

        given decoder.Ctx = decoder.Ctx(freshCopy(bytes), w, h, chan)
        // TODO: Revisiter precond
        // sorry(decoder.rangesInv(oldDecoded.index.length, oldDecoded.pixels.length, 0, outPos0, oldDecoded.pxPos)) // TODO
        val (ix1, pix1, decIter1) = decodeRangePureLemma(oldDecoded.index, oldDecoded.pixels, pxPrev, outPos0, outPos2, oldDecoded.pxPos)
        assert(decIter1.pxPos == decodedPreRec.pxPos)
        assert(decIter1.inPos == decodedPreRec.inPos)
        assert(decIter1.inPos == outPos2)
        assert(decIter1.px == px)

        assert(decodedPreRec.pxPos + chan * run1 == pxPos + chan)
        assert(decodedPreRec.pxPos < pixels.length)
        assert(decIter1.pxPos + chan <= pixels.length)
        assert(decIter1.pxPos < pixels.length && decIter1.pxPos + chan <= pixels.length)
        assert(ix1 == decodedPreRec.index)
        assert(pix1 == decodedPreRec.pixels)

        assert(decodedPreRec.index.length == 64 && decodedPreRec.pixels.length == pixels.length)
        assert(HeaderSize <= outPos2 && outPos2 <= bytes.length - Padding)
        assert(outPos2 <= bytes.length)
        assert(0 <= decodedPreRec.pxPos && decodedPreRec.pxPos <= decodedPreRec.pixels.length)
        assert(decodedPreRec.pxPos % chan == 0)
        assert(decodedPreRec.index.length == 64)
        assert(decodedPreRec.pixels.length == pixels.length)
        sorry(decodedPreRec.pixels.length == w * h * chan) // TODO
        sorry(decodedPreRec.pixels.length % chan == 0) // TODO
        // TODO: Revister precond
        // sorry(decoder.rangesInv(decodedPreRec.index.length, decodedPreRec.pixels.length, 0, outPos2, decodedPreRec.pxPos)) // TODO
        val (ix2, pix2, decIter2) = decodeRangePureLemma(decodedPreRec.index, decodedPreRec.pixels, px, outPos2, outPosRes, decodedPreRec.pxPos)
        assert(decIter2.pxPos == decoded.pxPos)
        assert(decIter2.inPos == decoded.inPos)
        assert(ix2 == decoded.index)
        assert(pix2 == decoded.pixels)

        assert(oldDecoded.pxPos % chan == 0)
        assert(HeaderSize <= outPos0 && outPos0 <= bytes.length)
        assert(oldDecoded.index.length == 64)
        assert(oldDecoded.pixels.length == pixels.length)
        assert(oldDecoded.pixels.length == w * h * chan)
        sorry(oldDecoded.pixels.length % chan == 0) // TODO
        assert(0 <= oldDecoded.pxPos && oldDecoded.pxPos <= oldDecoded.pixels.length)
        // TODO: Revister precond
        // assert(decoder.rangesInv(oldDecoded.index.length, oldDecoded.pixels.length, 0, outPos0, oldDecoded.pxPos))
        val (ix3, pix3, decIter3) = decodeRangePureLemma(oldDecoded.index, oldDecoded.pixels, pxPrev, outPos0, outPosRes, oldDecoded.pxPos)

        assert(outPosRes <= bytes.length - Padding)
        assert(outPos0 < outPos2)
        assert(outPos2 < outPosRes)
        assert(ix1 == decodedPreRec.index)
        assert(pix1 == decodedPreRec.pixels)
        assert(decIter1.px == px)
        assert(decIter1.inPos == outPos2)
        decodeRangePureMergedLemma(oldDecoded.index, oldDecoded.pixels, pxPrev, outPos0, outPos2, outPosRes, oldDecoded.pxPos) // 4 very slow (~120s)
        assert(ix2 == ix3)
        assert(pix2 == pix3)
        assert(decIter2 == decIter3)

        assert(decIter3.pxPos == decoded.pxPos)
        assert(decIter3.inPos == decoded.inPos)
        assert(ix3 == decoded.index)
        assert(pix3 == decoded.pixels)

        check(decodeEncodeProp(bytes, pxPrev, outPos0, outPosRes, oldDecoded, pxRes, decoded)) // Slow (~80s)
      }
      check(oldBytes.length == bytes.length)
      check(decodeEncodeProp(bytes, pxPrev, outPos0, outPosRes, oldDecoded, pxRes, decoded))

      arraysEqDropRightLemma(bytesPreRec, bytes, 0, outPos0, outPos2)
      arraysEqTransLemma(oldBytes, bytesPreRec, bytes, 0, outPos0)
      check(arraysEq(oldBytes, bytes, 0, outPos0))

      (pxRes, outPosRes)
    } else {
      check(outPos0 < outPos2) // TODO: Comment arrive-t-il à déduire cette prop?!?!?
      check(oldBytes.length == bytes.length)
      check(arraysEq(oldBytes, bytes, 0, outPos0))
      (px, outPos2)
    }
  }.ensuring { case (pxRes, outPosRes) =>
    bytes.length == maxSize &&&
    index.length == 64 &&&
    index == decoded.index &&&
    decoded.pixels.length == pixels.length &&&
    HeaderSize <= outPosRes &&& outPosRes <= maxSize - Padding &&&
    outPos0 < outPosRes &&&
    old(bytes).length == bytes.length &&&
    arraysEq(old(bytes), bytes, 0, outPos0) &&& // TODO: Precond 2 ~60s
    decodeEncodeProp(bytes, pxPrev, outPos0, outPosRes, old(decoded), pxRes, decoded) // Precond 4 slow (~90s)
  }

  case class EncodeSingleStepResult(px: Int, outPos: Long, run: Long, decoded: Decoded)

  @opaque
  def encodeSingleStep(index: Array[Int], bytes: Array[Byte], pxPrev: Int, run0: Long, outPos0: Long, pxPos: Long, decoded: Decoded)(using Ctx): (Int, Long, Long) = {
    require(rangesInv(index.length, bytes.length, run0, outPos0, pxPos))
    require(pxPos + chan <= pixels.length)
    require(positionsIneqInv(run0, outPos0, pxPos))
    require((chan == 3) ==> (Pixel.a(pxPrev) == 255.toByte))
    require(decoded.inPos == outPos0)
    require(decoded.index == index)
    require(decoded.pixels.length == pixels.length)
    require(pxPosInv(decoded.pxPos))
    require(decoded.pxPos + chan <= decoded.pixels.length)
    require(decoded.pxPos <= pxPos && decoded.pxPos + chan * run0 == pxPos)
    require(arraysEq(decoded.pixels, pixels, 0, decoded.pxPos))
    require((run0 > 0) ==> samePixelsForall(pixels, pxPrev, decoded.pxPos, pxPos, chan)) // En gros, que depuis dec.pxPos jusqu'a pxPos, on a bien pxPrev (run ne triche pas)

    assert(decoded.index.length == 64)

    val px =
      if (chan == 4) read32(pixels, pxPos.toInt)
      else {
        assert(chan == 3 && Pixel.a(pxPrev) == 255.toByte)
        Pixel.fromRgba(pixels(pxPos.toInt), pixels(pxPos.toInt + 1), pixels(pxPos.toInt + 2), Pixel.a(pxPrev)) // TODO: Pour un bug vicieux, changer 255 en 0
      }
    assert((chan == 3) ==> (Pixel.a(px) == Pixel.a(pxPrev)))
    assert(samePixels(pixels, px, pxPos, chan))
    given li: LoopIter = LoopIter(px, pxPrev, pxPos)

    val runUpd = updateRun(bytes, run0, outPos0)
    withinBoundsLemma(run0, outPos0, pxPos)
    assert((run0 + bool2int(px == pxPrev) > 0 && runUpd.reset) ==> updateRunProp(bytes, run0, outPos0, runUpd))
    val run1 = runUpd.run
    val outPos1 = runUpd.outPos

    val indexPre = freshCopy(index)

    val outPos2 = if (px != pxPrev) {
      assert(run1 == 0)
      assert(bool2int(px == pxPrev) == 0)

      ghostExpr {
        if (run0 == 0) {
          positionsIneqIncrementedLemma(run1, outPos1, pxPos)
          check(positionsIneqInv(run1, outPos1 + chan + 1, pxPos + chan))
        } else {
          assert(runUpd.reset && outPos1 <= outPos0 + 2 && run0 > 0)
          assert(chan * (outPos0 - HeaderSize + chan) <= (chan + 1) * pxPos)
          assert(chan * (outPos0 - HeaderSize + chan) + (chan + 1) * chan <= (chan + 1) * pxPos + (chan + 1) * chan)
          assert(chan * (outPos0 - HeaderSize + chan + chan + 1) <= (chan + 1) * (pxPos + chan))
          assert((chan * (outPos1 - HeaderSize + chan + 1) <= (chan + 1) * (pxPos + chan)) because (chan >= 3 && outPos1 <= outPos0 + 2))
          check(positionsIneqInv(0, outPos1 + chan + 1, pxPos + chan))
        }
        assert(positionsIneqInv(0, outPos1 + chan + 1, pxPos + chan))
      }

      val bytesPreEncNoRun = freshCopy(bytes)
      val outPos2 = encodeNoRun(index, bytes, outPos1)
      check(positionsIneqInv(0, outPos2, pxPos + chan))
      check(HeaderSize <= outPos2 && outPos1 < outPos2 && outPos2 <= maxSize - Padding)
      check(rangesInv(index.length, bytes.length, 0, outPos1, pxPos))

      // Note: bool2int(px == pxPrev) == 0
      check(((run0 > 0 && runUpd.reset) ==> updateRunProp(bytes, run0, outPos0, runUpd)) because {
        if (run0 > 0 && runUpd.reset) {
          updateRunPropBytesEqLemma(bytesPreEncNoRun, run0, outPos0, runUpd, bytes)
          trivial
        } else trivial
      })

      assert((outPos2 <= bytes.length - Padding) because (bytes.length == maxSize))
      check(positionsIneqInv(0, outPos1, pxPos))
      check(encodeNoRunProp(indexPre, index, bytes, outPos1, outPos2))

      outPos2
    } else {
      ghostExpr {
        if (runUpd.reset) {
          assert(outPos1 <= outPos0 + 2)
          assert(run1 == 0)
          assert(chan * (outPos0 - HeaderSize + run0 * chan) <= (chan + 1) * pxPos)
          assert(chan * (outPos0 - HeaderSize + run0 * chan) + (chan + 1) * chan <= (chan + 1) * pxPos + (chan + 1) * chan)
          assert(chan * (outPos0 - HeaderSize + run0 * chan + chan + 1) <= (chan + 1) * (pxPos + chan))
          assert((chan * (outPos1 - HeaderSize) <= (chan + 1) * (pxPos + chan)) because (chan >= 3 && outPos1 <= outPos0 + 2 && run0 >= 0))
          check(positionsIneqInv(run1, outPos1, pxPos + chan))
        } else {
          assert(outPos1 == outPos0 && run1 == run0 + 1 && run0 < 0x2020)
          assert(positionsIneqInv(run0, outPos0, pxPos))
          assert(chan * ((outPos0 - HeaderSize) + chan * run0) <= (chan + 1) * pxPos)
          assert(chan * ((outPos0 - HeaderSize) + chan * run0) + (chan + 1) * chan <= (chan + 1) * pxPos + (chan + 1) * chan)
          assert(chan * ((outPos0 - HeaderSize) + chan * run0 + chan + 1) <= (chan + 1) * pxPos + (chan + 1) * chan)
          assert(chan * ((outPos0 - HeaderSize) + chan * (run0 + 1)) <= (chan + 1) * pxPos + (chan + 1) * chan)
          assert((
            chan * ((outPos1 - HeaderSize) + chan * (run0 + 1)) <=
              (chan + 1) * pxPos + (chan + 1) * chan) because (outPos1 == outPos0))
          assert((chan * ((outPos1 - HeaderSize) + chan * (run0 + 1)) <= (chan + 1) * (pxPos + chan)) because ((chan + 1) * pxPos + (chan + 1) * chan == (chan + 1) * (pxPos + chan)))
          check(positionsIneqInv(run1, outPos1, pxPos + chan) because (run1 == run0 + 1))
        }
      }
      check(rangesInv(index.length, bytes.length, run1, outPos1, pxPos))
      check(positionsIneqInv(run1, outPos1, pxPos + chan))
      outPos1
    }
    assert(HeaderSize <= outPos2 && outPos2 <= maxSize - Padding)
    assert((px != pxPrev) ==> (outPos1 < outPos2))
    assert((outPos2 <= bytes.length - Padding) because (bytes.length == maxSize))
    assert((run0 + bool2int(px == pxPrev) > 0 && runUpd.reset) ==> updateRunProp(bytes, run0, outPos0, runUpd))
    assert((px != pxPrev) ==> encodeNoRunProp(indexPre, index, bytes, outPos1, outPos2))

    val newDecoded = if (run0 > 0 && runUpd.reset && px != pxPrev) {  // Note: bool2int(px == pxPrev) == 0
      check(outPos1 < outPos2)
      assert(updateRunProp(bytes, run0, outPos0, runUpd))
      assert(encodeNoRunProp(indexPre, index, bytes, outPos1, outPos2))
      assert(indexPre.updated(colorPos(px), px) == index)

      assert(decoded.pxPos + chan * run0 <= pixels.length)
      val decoded1 = decodeUpdateRunPass(bytes, run0, outPos0, runUpd, decoded)
      assert(arraysEq(pixels, decoded1.pixels, 0, decoded1.pxPos))
      arraysEqDropLeftLemma(pixels, decoded1.pixels, 0, pxPos, decoded1.pxPos)
      arraysEqSymLemma(pixels, decoded1.pixels, 0, pxPos)
      assert(arraysEq(decoded1.pixels, pixels, 0, pxPos))
      assert(decoded1.index == indexPre)
      val decoded2 = decodeEncodeNoRunPass(indexPre, index, bytes, outPos1, outPos2, decoded1)

      assert(decoded1.pxPos == decoded.pxPos + chan * run0)
      assert(decoded2.pxPos == decoded1.pxPos + chan)
      assert(decoded2.pxPos == decoded.pxPos + chan * run0 + chan)
      assert(decoded2.pxPos == decoded.pxPos + chan * (run0 + 1))
      assert(decoded.pxPos + chan * run0 + chan == pxPos + chan)
      assert(decoded.pxPos + chan * (run0 + 1) == pxPos + chan)
      assert(pxPos + chan <= pixels.length)
      assert(decoded2.pxPos <= pixels.length)
      assert(arraysEq(pixels, decoded2.pixels, 0, decoded2.pxPos))
      assert(decoded2.index == decoded1.index.updated(colorPos(px), px))

      given decoder.Ctx = decoder.Ctx(freshCopy(bytes), w, h, chan)
      assert(decoded.pixels.length == pixels.length)
      assert(pixels.length % chan == 0)
      assert(0 <= decoded.pxPos && decoded.pxPos <= decoded.pixels.length)
      assert(decoded.pxPos % chan == 0)
      assert(w * h * chan == decoded.pixels.length)
      assert(decoded.pixels.length % chan == 0)
      assert(HeaderSize <= outPos0 && outPos0 <= bytes.length - Padding)
      assert(decoded.index.length == 64)
      // TODO: Revister precond
      // assert(decoder.rangesInv(decoded.index.length, decoded.pixels.length, 0, outPos0, decoded.pxPos))
      assert(decoded.pxPos < decoded.pixels.length)
      assert(decoded.pxPos + chan <= decoded.pixels.length)
      assert(outPos0 < outPos1 && outPos1 <= bytes.length - Padding)
      val (ix1, pix1, decIter1) = decodeRangePureLemma(decoded.index, decoded.pixels, pxPrev, outPos0, outPos1, decoded.pxPos)
      assert(decIter1.pxPos == decoded1.pxPos)
      assert(decIter1.inPos == outPos1)

      decoder.doDecodeNext(decoded.index, pxPrev, outPos0) match {
        case (decoder.DecodedNext.Run(r), inPos) =>
          check(decIter1.px == pxPrev) // Very Slow (~90s)
          ()
        case _ =>
          check(false)
          ()
      }
      assert(decIter1.px == pxPrev)
      assert(ix1 == decoded1.index)
      assert(pix1 == decoded1.pixels)

      // TODO: Revister precond
      // assert(decoder.rangesInv(decoded1.index.length, decoded1.pixels.length, 0, outPos1, decoded1.pxPos))
      assert(decoded1.pxPos + chan <= decoded1.pixels.length)
      assert(outPos1 < outPos2 && outPos2 <= bytes.length - Padding)
      val (ix2, pix2, decIter2) = decodeRangePureLemma(decoded1.index, decoded1.pixels, decIter1.px, outPos1, outPos2, decoded1.pxPos)
      assert(decIter2.pxPos == decoded2.pxPos)
      assert(decIter2.inPos == outPos2)
      assert(ix2 == decoded2.index)
      assert(pix2 == decoded2.pixels)

      assert(decIter1.pxPos == decoded1.pxPos && decoded1.pxPos == decoded.pxPos + chan * run0)
      assert(decIter1.pxPos == decoded.pxPos + chan * run0)
      assert(decoded.pxPos + chan * run0 == pxPos)
      assert(decIter1.pxPos == pxPos)

      val (ix3, pix3, decIter3) = decodeRangePureLemma(decoded.index, decoded.pixels, pxPrev, outPos0, outPos2, decoded.pxPos)
      assert(decIter3.pxPos % chan == 0) // Very Slow (~90s)
      assert(pxPos < pixels.length && pxPos + chan <= pixels.length)
      assert(decIter1.pxPos < decoded.pixels.length)
      assert(decIter1.pxPos + chan <= decoded.pixels.length)
      decodeRangePureMergedLemma(decoded.index, decoded.pixels, pxPrev, outPos0, outPos1, outPos2, decoded.pxPos)
      assert(ix3 == decoded2.index)
      assert(pix3 == decoded2.pixels)
      assert(decIter3.pxPos == decoded2.pxPos)
      assert(decIter3.inPos == outPos2)

      assert(decoded2.pxPos == pxPos + chan)

      assert(rangesInv(index.length, bytes.length, 0, outPos0, pxPos))
      assert(pxPos + chan <= pixels.length)
      assert(decoded.pixels.length == pixels.length)
      assert(0 <= decoded.pxPos && decoded.pxPos < decoded.pixels.length)
      assert(decoded.pxPos + chan <= decoded.pixels.length)
      assert(decoded.pxPos % chan == 0)
      assert(outPos0 < outPos2 && outPos2 <= bytes.length - Padding)

      assert(decIter3.pxPos <= decoded.pixels.length)
      assert(decIter3.inPos == outPos2)

      // assert(arraysEq(pixels, pix3, 0, decIter3.pxPos))
      assert(arraysEq(pixels, decoded2.pixels, 0, decoded2.pxPos))
      assert(decIter3.pxPos == pxPos + chan)
      assert(pix3 == decoded2.pixels && decoded2.pxPos == pxPos + chan)
      assert(arraysEq(pixels, pix3, 0, decIter3.pxPos))

      assert(decIter3.remainingRun == 0) // Very slow (~150s)
      check(decodeEncodeProp(bytes, pxPrev, outPos0, outPos2, decoded, px, decoded2)) // Very slow (~120s)
      check(index == decoded2.index)

      assert(run1 == 0)
      check(decoded2.pxPos + chan * run1 == pxPos + chan)

      freshCopy(decoded2)
    } else if (!(run0 > 0 && runUpd.reset) && px != pxPrev) { // Note: bool2int(px == pxPrev) == 0
      check(outPos0 == outPos1)
      assert(encodeNoRunProp(indexPre, index, bytes, outPos1, outPos2))
      assert(indexPre.updated(colorPos(px), px) == index)
      val decoded2 = decodeEncodeNoRunPass(indexPre, index, bytes, outPos1, outPos2, decoded)
      assert(decoded2.pixels.length == pixels.length)
      assert(decoded2.pxPos % chan == 0)
      assert(decoded2.pxPos == decoded.pxPos + chan)
      assert(arraysEq(pixels, decoded2.pixels, 0, decoded2.pxPos))
      check(decodeEncodeProp(bytes, pxPrev, outPos0, outPos2, decoded, px, decoded2))
      check(index == decoded2.index)

      assert(run0 == 0 && run1 == 1)
      assert(decoded.pxPos == pxPos)
      check(decoded2.pxPos + chan * run1 == pxPos + chan)

      freshCopy(decoded2)
    } else if (run0 + 1 > 0 && runUpd.reset && px == pxPrev) { // Note: bool2int(px == pxPrev) == 1
      assert(decoded.pxPos + chan * run0 <= pixels.length)
      check(outPos1 == outPos2)
      assert(updateRunProp(bytes, run0, outPos0, runUpd))
      val decoded2 = decodeUpdateRunPass(bytes, run0, outPos0, runUpd, decoded)
      assert(decoded2.pixels.length == pixels.length)
      assert(decoded2.pxPos == decoded.pxPos + chan * (run0 + 1))
      assert(decoded.pxPos + chan * run0 == pxPos)
      assert(decoded.pxPos + chan * run0 + chan == pxPos + chan)
      assert(decoded.pxPos + chan * (run0 + 1) == pxPos + chan)
      assert(decoded2.pxPos == pxPos + chan)
      assert(decoded2.pxPos % chan == 0)
      assert(arraysEq(pixels, decoded2.pixels, 0, decoded2.pxPos))
      check(decodeEncodeProp(bytes, pxPrev, outPos0, outPos2, decoded, px, decoded2))
      check(index == decoded2.index)

      assert(run1 == 0)
      check(decoded2.pxPos + chan * run1 == pxPos + chan)

      freshCopy(decoded2)
    } else {
      check(outPos0 == outPos1 && outPos1 == outPos2)
      check(run1 == run0 + 1 && px == pxPrev)

      assert(decoded.pxPos <= pxPos && decoded.pxPos + chan * run0 == pxPos)
      assert(decoded.pxPos + chan * run0 + chan == pxPos + chan)
      assert(decoded.pxPos + chan * (run0 + 1) == pxPos + chan)
      check(decoded.pxPos + chan * run1 == pxPos + chan)

      freshCopy(decoded)
    }

    check(index == newDecoded.index)
    check((outPos0 < outPos2) ==> decodeEncodeProp(bytes, pxPrev, outPos0, outPos2, decoded, px, newDecoded))

    check(rangesInv(index.length, bytes.length, run1, outPos2, pxPos))
    check(positionsIneqInv(run1, outPos2, pxPos + chan))

    decoded.index = freshCopy(newDecoded.index)
    decoded.pixels = freshCopy(newDecoded.pixels)
    decoded.inPos = newDecoded.inPos
    decoded.pxPos = newDecoded.pxPos
    (px, outPos2, run1)
  }.ensuring { case (px, outPos2, run1) =>
    // Bytes and index length are unchanged
    bytes.length == maxSize &&&
    index.length == 64 &&&
    // Range for outPos2
    outPos0 <= outPos2 &&&
    HeaderSize <= outPos2 &&& outPos2 <= maxSize - Padding &&&
    // Run-related props
    0 <= run1 &&& run1 < 0x2020 &&&
    ((run1 > 0) ==> (bytes == old(bytes) && outPos2 == outPos0)) &&&
    ((pxPos == pxEnd) ==> (run1 == 0)) &&&
    // Ranges et inequality still holding
    positionsIneqInv(run1, outPos2, pxPos + chan) &&&
    rangesInv(index.length, bytes.length, run1, outPos2, pxPos) &&&
    // Alpha-channel unchanged when we only have 3 channels
    ((chan == 3) ==> (Pixel.a(px) == 255.toByte)) &&&
    index == decoded.index &&&
    decoded.pixels.length == pixels.length &&&
    // TODO: Mettre des comms
    pxPosInv(decoded.pxPos) &&&
    decoded.pxPos + chan * run1 == pxPos + chan &&&
    ((outPos0 < outPos2) ==> decodeEncodeProp(bytes, pxPrev, outPos0, outPos2, old(decoded), px, decoded)) &&&
    ((outPos0 == outPos2) ==> (old(decoded) == decoded && run1 == run0 + 1 && px == pxPrev)) &&&
    samePixels(pixels, px, pxPos, chan) &&&
    arraysEq(old(bytes), bytes, 0, outPos0)
  }

  // TODO: Name
  def decodeEncodeProp(bytes: Array[Byte],
                       pxPrev: Int,
                       outPos0: Long,
                       outPos2: Long,
                       decoded: Decoded,
                       px: Int,
                       newDecoded: Decoded)(using Ctx): Boolean = {
    require(outPosInv(outPos0))
    require(outPosInv(outPos2))
    require(decoded.pixels.length == pixels.length)
    require(decoded.index.length == 64)
    require(pxPosInv(decoded.pxPos))
    require(decoded.pxPos + chan <= decoded.pixels.length)
    require(outPos0 < outPos2)

    given decoder.Ctx = decoder.Ctx(freshCopy(bytes), w, h, chan)
    assert(decoded.pixels.length == w * h * chan)
    assert(decoded.pixels.length % chan == 0)
    assert(HeaderSize <= outPos0 && outPos0 <= bytes.length)
    val (decIndex, decPixels, decIter) = decodeRangePureLemma(decoded.index, decoded.pixels, pxPrev, outPos0, outPos2, decoded.pxPos)

    decoded.pxPos < decIter.pxPos &&
    decIter.pxPos <= decoded.pixels.length &&
    decIter.pxPos % chan == 0 &&
    decIter.inPos == outPos2 &&
    arraysEq(pixels, decPixels, 0, decIter.pxPos) &&
    decIter.remainingRun == 0 &&
    decIter.pxPos == newDecoded.pxPos &&
    decIter.inPos == newDecoded.inPos &&
    decIndex == newDecoded.index &&
    decPixels == newDecoded.pixels &&
    decIter.px == px
  }

  @opaque
  def decodeEncodePropBytesEqLemma(bytes1: Array[Byte],
                                   bytes2: Array[Byte],
                                   pxPrev: Int,
                                   pxPos: Long,
                                   outPos0: Long,
                                   outPos2: Long,
                                   decoded: Decoded,
                                   px: Int,
                                   newDecoded: Decoded)(using Ctx): Unit = {
    require(bytes1.length == maxSize)
    require(outPosInv(outPos0))
    require(outPosInv(outPos2))
    require(pxPosInv(pxPos))
    require(pxPos + chan <= pixels.length)
    require(decoded.pixels.length == pixels.length)
    require(decoded.index.length == 64)
    require(decoded.pxPos + chan <= decoded.pixels.length)
    require(pxPosInv(decoded.pxPos))
    require(outPos0 < outPos2)
    require(decodeEncodeProp(bytes1, pxPrev, outPos0, outPos2, decoded, px, newDecoded))
    require(bytes1.length == bytes2.length)
    require(arraysEq(bytes1, bytes2, outPos0, outPos2))
    require(0 <= newDecoded.pxPos && newDecoded.pxPos < decoded.pixels.length && newDecoded.pxPos + chan <= decoded.pixels.length)

    val ctx1 = decoder.Ctx(freshCopy(bytes1), w, h, chan)
    assert(decoded.pixels.length % chan == 0)
    assert(decoded.pixels.length == w * h * chan)
    assert(outPos0 <= bytes1.length)
    // TODO: Revister precond
    // assert(decoder.rangesInv(decoded.index.length, decoded.pixels.length, 0, outPos0, decoded.pxPos)(using ctx1))
    val (ix1, pix1, decIter1) = decodeRangePureLemma(decoded.index, decoded.pixels, pxPrev, outPos0, outPos2, decoded.pxPos)(using ctx1)
    assert(decIter1.pxPos == newDecoded.pxPos)
    assert(decIter1.pxPos < pixels.length && decIter1.pxPos + chan <= pixels.length)
    assert(decIter1.inPos == outPos2)

    val ctx2 = decoder.Ctx(freshCopy(bytes2), w, h, chan)
    decodeRangePureBytesEqLemma(decoded.index, decoded.pixels, pxPrev, outPos0, outPos2, decoded.pxPos, bytes2)(using ctx1)
    val (ix2, pix2, decIter2) = decodeRangePureLemma(decoded.index, decoded.pixels, pxPrev, outPos0, outPos2, decoded.pxPos)(using ctx2)
    assert(ix1 == ix2)
    assert(pix1 == pix2)
    assert(decIter1 == decIter2)
    check(decodeEncodeProp(bytes2, pxPrev, outPos0, outPos2, decoded, px, newDecoded))
  }.ensuring(_ => decodeEncodeProp(bytes2, pxPrev, outPos0, outPos2, decoded, px, newDecoded))

  @opaque
  def decodeUpdateRunPass(bytes: Array[Byte], run0: Long, outPos0: Long, ru: RunUpdate, decoded: Decoded)(using Ctx, LoopIter): Decoded = {
    require(bytes.length == maxSize)
    require(runInv(run0))
    require(outPosInv(outPos0))
    require(pxPosInv(pxPos))
    require(pxPos + chan <= pixels.length)
    require(outPos0 < bytes.length - Padding)
    val run = run0 + bool2int(px == pxPrev)
    require(run > 0)
    require(updateRunProp(bytes, run0, outPos0, ru))
    require(outPos0 < ru.outPos && ru.outPos <= bytes.length - Padding)
    require(decoded.index.length == 64)
    require(decoded.pixels.length == pixels.length)
    require(pxPosInv(decoded.pxPos))
    require(decoded.pxPos + chan <= decoded.pixels.length)
    require(decoded.pxPos + chan * run0 == pxPos)
    require(arraysEq(decoded.pixels, pixels, 0, decoded.pxPos))
    require(samePixels(pixels, px, pxPos, chan))
    require((run0 > 0) ==> samePixelsForall(pixels, pxPrev, decoded.pxPos, pxPos, chan))

    assert(decoded.pxPos + chan * run0 + chan <= pixels.length)
    assert(pxPos % chan == 0 && pixels.length % chan == 0) // Slow (~35s)

    given dctx: decoder.Ctx = decoder.Ctx(freshCopy(bytes), w, h, chan)
    assert(decoded.pixels.length == w * h * chan)
    assert(decoded.pixels.length % chan == 0)
    assert(HeaderSize <= outPos0 && outPos0 <= bytes.length)
    val (decIndex, decPixels, decIter) = decodeRangePureLemma(decoded.index, decoded.pixels, pxPrev, outPos0, ru.outPos, decoded.pxPos)
    check(decIter.pxPos % chan == 0)
    assert(decIndex == decoded.index) // Slow (~1m)
    assert(updateRunProp(bytes, run0, outPos0, ru))
    check(decIter.px == pxPrev) // Slow (~37s)
    check(decIter.inPos == ru.outPos) // Slow (~25s)
    assert((decoded.pxPos + chan + chan * (run - 1) <= decoded.pixels.length) ==> (decIter.remainingRun == 0 && decIter.pxPos == decoded.pxPos + chan * run)) // Slow (1m15)
    assert(run - 1 <= run0)
    assert(decoded.pxPos + chan * run <= decoded.pxPos + chan * run0 + chan)
    assert(decoded.pxPos + chan * run == decoded.pxPos + chan + chan * (run - 1))
    assert(decoded.pxPos + chan + chan * (run - 1) <= pixels.length)
    check(decIter.remainingRun == 0)
    check(decIter.pxPos == decoded.pxPos + chan * run)

    check(decoded.pxPos < decIter.pxPos)
    check(decIter.pxPos <= decoded.pixels.length) // Slow (~28s)
    check(decIter.pxPos % chan == 0) // Slow (lol) (30s)
    check(decoded.pixels.length == decPixels.length)
    check(decoded.pixels.length == decPixels.length)
    assert(arraysEq(decoded.pixels, decPixels, 0, decoded.pxPos)) // Slow (~25s)
    assert(samePixelsForall(decPixels, pxPrev, decoded.pxPos, decIter.pxPos, chan)) // Slow (~35s)

    arraysEqSymLemma(decoded.pixels, pixels, 0, decoded.pxPos)
    arraysEqTransLemma(pixels, decoded.pixels, decPixels, 0, decoded.pxPos)
    assert(arraysEq(pixels, decPixels, 0, decoded.pxPos))

    val pxPosPlusChan = pxPos + chan
    assert(pxPosPlusChan <= pixels.length)
    sorry(pxPosPlusChan % chan == 0) // TODO
    samePixelsSingleElementRange(pixels, px, pxPos, chan)
    assert(samePixelsForall(pixels, px, pxPos, pxPosPlusChan, chan))
    if (run0 == 0) {
      assert(px == pxPrev)
      assert(decoded.pxPos == pxPos)
      assert(decIter.pxPos == decoded.pxPos + chan)
      assert(decIter.pxPos == pxPos + chan)
      assert(decIter.pxPos == pxPosPlusChan)
      assert(samePixelsForall(decPixels, px, pxPos, pxPosPlusChan, chan))
      samePixelsForallArraysEq(pixels, decPixels, px, pxPos, pxPosPlusChan, chan)
      arraysEqCombinedLemma(pixels, decPixels, 0, pxPos, pxPosPlusChan)
      check(arraysEq(pixels, decPixels, 0, decIter.pxPos))
    } else {
      assert(samePixelsForall(pixels, pxPrev, decoded.pxPos, pxPos, chan))
      assert(decoded.pxPos + chan * run0 == pxPos && decIter.pxPos == decoded.pxPos + chan * run) // From previous assertions
      assert(decoded.pxPos == pxPos - chan * run0)
      assert(decIter.pxPos == pxPos - chan * run0 + chan * run)
      assert(decIter.pxPos == pxPos + chan * bool2int(px == pxPrev))
      if (px == pxPrev) {
        assert(decIter.pxPos == pxPos + chan)
        samePixelsForallCombinedLemma(pixels, px, decoded.pxPos, pxPos, pxPosPlusChan, chan)
        assert(samePixelsForall(pixels, px, decoded.pxPos, decIter.pxPos, chan))
        samePixelsForallArraysEq(pixels, decPixels, px, decoded.pxPos, decIter.pxPos, chan)
        assert(arraysEq(pixels, decPixels, decoded.pxPos, decIter.pxPos))
        arraysEqCombinedLemma(pixels, decPixels, 0, decoded.pxPos, decIter.pxPos)
        check(arraysEq(pixels, decPixels, 0, decIter.pxPos))
      } else {
        assert(decIter.pxPos == pxPos)
        assert(samePixelsForall(pixels, pxPrev, decoded.pxPos, decIter.pxPos, chan))
        samePixelsForallArraysEq(pixels, decPixels, pxPrev, decoded.pxPos, decIter.pxPos, chan)
        assert(arraysEq(pixels, decPixels, decoded.pxPos, decIter.pxPos))
        arraysEqCombinedLemma(pixels, decPixels, 0, decoded.pxPos, decIter.pxPos)
        check(arraysEq(pixels, decPixels, 0, decIter.pxPos))
      }
      check(arraysEq(pixels, decPixels, 0, decIter.pxPos))
    }
    check(arraysEq(pixels, decPixels, 0, decIter.pxPos))

    Decoded(freshCopy(decIndex), freshCopy(decPixels), decIter.inPos, decIter.pxPos)
  }.ensuring { newDecoded =>
    newDecoded.pxPos == decoded.pxPos + chan * (run0 + bool2int(px == pxPrev)) &&&
    newDecoded.pxPos % chan == 0 &&&
    newDecoded.inPos == ru.outPos &&&
    newDecoded.index == decoded.index &&&
    decodeEncodeProp(bytes, pxPrev, outPos0, ru.outPos, decoded, pxPrev, newDecoded)
  }

  def updateRunProp(bytes: Array[Byte], run0: Long, outPos0: Long, ru: RunUpdate)(using Ctx, LoopIter): Boolean = {
    require(bytes.length == maxSize)
    require(runInv(run0))
    require(outPosInv(outPos0))
    require(outPos0 < bytes.length - Padding)
    val run = run0 + bool2int(px == pxPrev)
    require(run > 0)

    val dummyIndex = Array.fill(64)(0)
    given decoder.Ctx = decoder.Ctx(freshCopy(bytes), w, h, chan)
    decoder.doDecodeNext(dummyIndex, pxPrev, outPos0) match {
      case (decoder.DecodedNext.Run(r), inPos) => r + 1 == run && inPos == ru.outPos
      case _ => false
    }
  }

  def updateRunPropBytesEqLemma(bytes: Array[Byte], run0: Long, outPos0: Long,
                                ru: RunUpdate, bytes2: Array[Byte])(using Ctx, LoopIter): Unit = {
    require(bytes.length == maxSize)
    require(runInv(run0))
    require(outPosInv(outPos0))
    require(pxPosInv(pxPos))
    require(pxPos + chan <= pixels.length)
    require(outPos0 < bytes.length - Padding)
    val run = run0 + bool2int(px == pxPrev)
    require(run > 0)
    require(updateRunProp(bytes, run0, outPos0, ru))
    require(bytes.length == bytes2.length)
    require(arraysEq(bytes, bytes2, 0, ru.outPos))
    require(outPos0 + 1 <= ru.outPos)
    require((run >= 33) ==> (outPos0 + 2 <= ru.outPos))

    val dctx1: decoder.Ctx = decoder.Ctx(freshCopy(bytes), w, h, chan)
    val dctx2: decoder.Ctx = decoder.Ctx(freshCopy(bytes2), w, h, chan)
    // TODO: Revister precond
//    assert(decoder.rangesInv(64, pixels.length, 0, outPos0, pxPos)(using dctx1))
//    assert(decoder.rangesInv(64, pixels.length, 0, outPos0, pxPos)(using dctx2))
    val dummyIndex = Array.fill(64)(0)
    val res1 = decoder.doDecodeNext(dummyIndex, pxPrev, outPos0)(using dctx1)
    val res2 = decoder.doDecodeNext(dummyIndex, pxPrev, outPos0)(using dctx2)

    val b1Bytes1 = bytes(outPos0.toInt).toInt & 0xff
    val b1Bytes2 = bytes2(outPos0.toInt).toInt & 0xff
    arraysEqAtIndex(bytes, bytes2, 0, ru.outPos, outPos0)
    assert(b1Bytes1 == b1Bytes2)
    assert((b1Bytes1 & Mask2) == OpRun)
    check(res1 == res2)
    check((outPos0 < bytes2.length - Padding) because (bytes.length == bytes2.length))
  }.ensuring(_ => updateRunProp(bytes2, run0, outPos0, ru))

  @inline
  def updateRun(bytes: Array[Byte], run0: Long, outPos0: Long)(using Ctx, LoopIter): RunUpdate = {
    require(bytes.length == maxSize)
    require(runInv(run0))
    require(outPosInv(outPos0))
    require(pxPosInv(pxPos))
    require(pxPos + chan <= pixels.length)
    require(positionsIneqInv(run0, outPos0, pxPos))

    withinBoundsLemma(run0, outPos0, pxPos)
    assert(outPos0 + run0 * chan + Padding <= maxSize)
    assert(outPos0 + 2 <= maxSize)

    var run = run0
    var outPos = outPos0

    if (px == pxPrev)
      run += 1

    var runReset = false
    if (run > 0 && (run == 62 || px != pxPrev || pxPos == pxEnd)) {
      val b1 = (OpRun | (run - 1)).toByte
      bytes(outPos.toInt) = b1
      outPos += 1
      check(decoder.decodeRun(b1) == run - 1)
      run = 0
      runReset = true
    }
    RunUpdate(runReset, run, outPos)
  } ensuring { ru =>
    old(bytes).length == bytes.length &&&
    runInv(ru.run) &&&
    outPosInv(ru.outPos) &&&
    (ru.reset ==> (ru.run == 0 && ru.outPos == outPos0 + 1)) &&&
    (!ru.reset ==> (ru.outPos == outPos0)) &&&
    ((px != pxPrev && run0 == 0) ==> (ru.run == 0)) &&&
    ((px == pxPrev && !ru.reset) ==> (ru.run == run0 + 1)) &&&
    ((run0 + bool2int(px == pxPrev) > 0 && ru.reset) ==> updateRunProp(bytes, run0, outPos0, ru))
    //((res.reset && run0 < 33) ==> (res.outPos == outPos0 + 1)) &&& // !!! Bien vu :)
    // ((res.reset && run0 >= 33) ==> (res.outPos == outPos0 + 2)) &&& // !!! Bien vu :)
  }

  // TODO: Name: this encodes when px != pxPrev
  @opaque
  def decodeEncodeNoRunPass(oldIndex: Array[Int], index: Array[Int], bytes: Array[Byte], outPos1: Long, outPos2: Long, decoded: Decoded)(using Ctx, LoopIter): Decoded = {
    require(oldIndex.length == 64)
    require(index.length == 64)
    require(bytes.length == maxSize)
    require(outPosInv(outPos1))
    require(outPosInv(outPos2))
    require(pxPosInv(pxPos))
    require(pxPos + chan <= pixels.length)
    require(positionsIneqInv(0, outPos1, pxPos))
    require(outPos1 < outPos2)
    require(decoded.index.length == 64)
    require(oldIndex == decoded.index)
    require(encodeNoRunProp(oldIndex, index, bytes, outPos1, outPos2))
    require(decoded.pixels.length == pixels.length)
    require(decoded.pxPos == pxPos)
    require(samePixels(pixels, px, pxPos, chan))
    require(arraysEq(decoded.pixels, pixels, 0, pxPos))
    require(px != pxPrev)

    assert(pxPos % chan == 0 && pixels.length % chan == 0)
    given decoder.Ctx = decoder.Ctx(freshCopy(bytes), w, h, chan)
    val (decIndex, decPixels, decIter) = decodeRangePureLemma(decoded.index, decoded.pixels, pxPrev, outPos1, outPos2, decoded.pxPos)
    check(decPixels.length == decoded.pixels.length)
    check(decoded.pxPos < decIter.pxPos)
    check(decIter.pxPos <= decoded.pixels.length)
    check(decIter.pxPos % chan == 0)
    check(decIter.inPos == outPos2)
    assert(decPixels.length % chan == 0)
    check(decIter.remainingRun == 0)
    check(decIter.pxPos == decoded.pxPos + chan)

    assert(encodeNoRunProp(oldIndex, index, bytes, outPos1, outPos2))
    check(decoded.index.updated(colorPos(px), px) == decIndex)
    assert(samePixels(decPixels, px, decoded.pxPos, chan)) // TODO: A quoi cela sert-il?

    assert(arraysEq(decoded.pixels, decPixels, 0, decoded.pxPos))
    arraysEqSymLemma(decoded.pixels, pixels, 0, pxPos)
    arraysEqTransLemma(pixels, decoded.pixels, decPixels, 0, pxPos)
    assert(arraysEq(pixels, decPixels, 0, pxPos))
    samePixelsSingleElementRange(pixels, px, pxPos, chan)
    samePixelsSingleElementRange(decPixels, px, pxPos, chan)
    samePixelsForallArraysEq(pixels, decPixels, px, pxPos, pxPos + chan, chan)
    assert(arraysEq(pixels, decPixels, pxPos, pxPos + chan))
    arraysEqCombinedLemma(pixels, decPixels, 0, pxPos, pxPos + chan)
    assert(arraysEq(pixels, decPixels, 0, pxPos + chan))
    check(arraysEq(pixels, decPixels, 0, decIter.pxPos) because (decIter.pxPos == pxPos + chan))

    Decoded(freshCopy(decIndex), freshCopy(decPixels), decIter.inPos, decIter.pxPos)
  }.ensuring { newDecoded =>
    newDecoded.pxPos % chan == 0 &&&
    newDecoded.inPos == outPos2 &&&
    newDecoded.pxPos == pxPos + chan &&&
    newDecoded.index == decoded.index.updated(colorPos(px), px) &&&
    decodeEncodeProp(bytes, pxPrev, outPos1, outPos2, decoded, px, newDecoded)
  }

  def encodeNoRunProp(oldIndex: Array[Int], index: Array[Int], bytes: Array[Byte], outPos1: Long, outPos2: Long)(using Ctx, LoopIter): Boolean = {
    require(oldIndex.length == 64)
    require(index.length == 64)
    require(bytes.length == maxSize)
    require(outPosInv(outPos1))
    require(outPosInv(outPos2))
    require(pxPosInv(pxPos))
    require(pxPos + chan <= pixels.length)
    require(positionsIneqInv(0, outPos1, pxPos))
    require(outPos1 < outPos2)

    given dctx: decoder.Ctx = decoder.Ctx(freshCopy(bytes), w, h, chan)
    withinBoundsLemma(0, outPos1, pxPos)
    assert(0 <= pxPos && pxPos <= pixels.length && w * h * chan == pixels.length && pixels.length % chan == 0)
    // TODO: Revister precond
//    assert(decoder.rangesInv(oldIndex.length, pixels.length, 0, outPos1, pxPos))

    decoder.doDecodeNext(oldIndex, pxPrev, outPos1) match {
      case (decoder.DecodedNext.DiffIndexColor(decodedPx), inPosRes) =>
        decodedPx == px && inPosRes == outPos2 && oldIndex.updated(colorPos(px), px) == index
      case _ => false
    }
  }

  // TODO: Adapt proofs to changed spec
  @opaque
  @inlineOnce
  def encodeNoRun(index: Array[Int], bytes: Array[Byte], outPos1: Long)(using Ctx, LoopIter): Long = {
    require(index.length == 64)
    require(bytes.length == maxSize)
    require(outPosInv(outPos1))
    require(pxPosInv(pxPos))
    require(pxPos + chan <= pixels.length)
    require(positionsIneqInv(0, outPos1, pxPos))
    require((chan == 3) ==> (Pixel.a(px) == Pixel.a(pxPrev)))

    withinBoundsLemma(0, outPos1, pxPos)
    assert(outPos1 + chan + 1 <= maxSize)

    positionsIneqIncrementedLemma(0, outPos1, pxPos)
    assert(positionsIneqInv(0, outPos1 + chan + 1, pxPos + chan)) // Needed for loopInvUpperOutPosLemma

    val indexPre = freshCopy(index)
    val bytesPre = freshCopy(bytes)

    val indexPos = colorPos(px)
    var newOutPos = outPos1

    if (index(indexPos) == px) {
      bytes(newOutPos.toInt) = (OpIndex | indexPos).toByte
      newOutPos += 1
      check(newOutPos <= maxSize - Padding)
      check(encodeNoRunProp(indexPre, index, bytes, outPos1, newOutPos))
    } else {
      index(indexPos) = px

      if (Pixel.a(px) == Pixel.a(pxPrev)) {
        // Note: these 5 variables are declared as signed char in the reference implementation
        val vr = ((Pixel.r(px).toInt & 0xff) - (Pixel.r(pxPrev).toInt & 0xff)).toByte
        val vg = ((Pixel.g(px).toInt & 0xff) - (Pixel.g(pxPrev).toInt & 0xff)).toByte
        val vb = ((Pixel.b(px).toInt & 0xff) - (Pixel.b(pxPrev).toInt & 0xff)).toByte
        val vgR = (vr - vg).toByte
        val vgB = (vb - vg).toByte

        if (vr > -3 && vr < 2 && vg > -3 && vg < 2 && vb > -3 && vb < 2) {
          val b1 = OpDiff | (((vr + 2) << 4) & 0xff) | (((vg + 2) << 2) & 0xff) | ((vb + 2) & 0xff)
          // TODO
//          check(decoder.decodeDiff(pxPrev, b1) == px)
          bytes(newOutPos.toInt) = b1.toByte
          newOutPos += 1
        } else if (vgR > -9 && vgR < 8 && vg > -33 && vg < 32 && vgB > -9 && vgB < 8) {
          val b1 = OpLuma | ((vg + 32) & 0xff)
          val b2 = (((vgR + 8) << 4) & 0xff) | ((vgB + 8) & 0xff)
          // TODO
//          check(decoder.decodeLuma(pxPrev, b1, b2) == px)
          bytes(newOutPos.toInt) = b1.toByte
          newOutPos += 1
          bytes(newOutPos.toInt) = b2.toByte
          newOutPos += 1
        } else {
          bytes(newOutPos.toInt) = OpRgb.toByte
          newOutPos += 1
          bytes(newOutPos.toInt) = Pixel.r(px)
          newOutPos += 1
          bytes(newOutPos.toInt) = Pixel.g(px)
          newOutPos += 1
          bytes(newOutPos.toInt) = Pixel.b(px)
          newOutPos += 1
        }

        loopInvUpperOutPosLemma(0, outPos1, pxPos + chan, newOutPos) // For precond. 2 of withinBoundsLemma2
        withinBoundsLemma2(0, newOutPos, pxPos + chan)
        check(newOutPos <= maxSize - Padding)
        check(encodeNoRunProp(indexPre, index, bytes, outPos1, newOutPos))

//        withinBoundsLemma(index.length, bytes.length, 0, outPos1, pxPos)
//        assert(outPos1 < maxSize - Padding)
//        check(decoder.decodeColor(bytes, pxPrev, b1, outPos1 + 1, chan) == (px, newOutPos))
//        loopInvUpperOutPosLemma(index.length, bytes.length, 0, outPos1, pxPos + chan, newOutPos) // For precond. 2 of withinBoundsLemma2
//        withinBoundsLemma2(index.length, bytes.length, 0, newOutPos, pxPos + chan)
//        check(newOutPos <= maxSize - Padding)
//        check(encodeNoRunProp(indexPre, index, bytes, outPos1, newOutPos))
      } else {
        bytes(newOutPos.toInt) = OpRgba.toByte
        newOutPos += 1
        bytes(newOutPos.toInt) = Pixel.r(px)
        newOutPos += 1
        bytes(newOutPos.toInt) = Pixel.g(px)
        newOutPos += 1
        bytes(newOutPos.toInt) = Pixel.b(px)
        newOutPos += 1
        bytes(newOutPos.toInt) = Pixel.a(px)
        newOutPos += 1

        loopInvUpperOutPosLemma(0, outPos1, pxPos + chan, newOutPos) // For precond. 2 of withinBoundsLemma2
        withinBoundsLemma2(0, newOutPos, pxPos + chan)
        check(newOutPos <= maxSize - Padding)
        check(encodeNoRunProp(indexPre, index, bytes, outPos1, newOutPos))
      }
    }
    assert(newOutPos <= outPos1 + chan + 1)
    check(newOutPos <= maxSize - Padding)
    loopInvUpperOutPosLemma(0, outPos1, pxPos + chan, newOutPos)
    check(rangesInv(index.length, bytes.length, 0, newOutPos, pxPos))
    check(positionsIneqInv(0, newOutPos, pxPos + chan))
    check(encodeNoRunProp(indexPre, index, bytes, outPos1, newOutPos))
    sorry(arraysEq(bytesPre, bytes, 0, outPos1)) // TODO
    check(arraysEq(bytesPre, bytes, 0, outPos1))
    newOutPos
  } ensuring { newOutPos =>
    old(bytes).length == bytes.length &&&
    outPosInv(newOutPos) &&&
    outPos1 < newOutPos &&&
    positionsIneqInv(0, newOutPos, pxPos + chan) &&&
    encodeNoRunProp(old(index), index, bytes, outPos1, newOutPos) &&&
    arraysEq(old(bytes), bytes, 0, outPos1)
  }

  /////////////////////////////////////////////////////////////////////////////////////////////////////

  @inline
  def maxSize(using ctx: Ctx): Long = ctx.maxSize

  @inline
  def pxEnd(using ctx: Ctx): Long = ctx.pxEnd

  @inline
  def w(using ctx: Ctx): Long = ctx.w

  @inline
  def h(using ctx: Ctx): Long = ctx.h

  @inline
  def chan(using ctx: Ctx): Long = ctx.chan

  @inline
  def pixels(using ctx: Ctx): Array[Byte] = ctx.pixels

  @inline
  def px(using li: LoopIter): Int = li.px

  @inline
  def pxPrev(using li: LoopIter): Int = li.pxPrev

  @inline
  def pxPos(using li: LoopIter): Long = li.pxPos
}
