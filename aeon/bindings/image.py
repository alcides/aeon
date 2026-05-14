from __future__ import annotations

import math
from typing import Any

import numpy as np
from PIL import Image
from PIL import ImageFilter
from PIL import ImageOps
from PIL.ImageDraw import Draw
from skimage.metrics import mean_squared_error as mse

from aeon.bindings.binding_utils import curried


def _lanczos_resample() -> Any:
    resampling = getattr(Image, "Resampling", None)
    if resampling is not None:
        return resampling.LANCZOS
    return Image.LANCZOS


def _transpose_flip_lr() -> Any:
    transpose = getattr(Image, "Transpose", None)
    if transpose is not None:
        return transpose.FLIP_LEFT_RIGHT
    return Image.FLIP_LEFT_RIGHT


def _transpose_flip_tb() -> Any:
    transpose = getattr(Image, "Transpose", None)
    if transpose is not None:
        return transpose.FLIP_TOP_BOTTOM
    return Image.FLIP_TOP_BOTTOM


@curried
def Image_mk(w, h, c):
    return Image.new("RGB", (w, h), c)


@curried
def Image_open(path):
    """Open an image and normalize to RGB so Color / pixel helpers stay consistent."""
    im = Image.open(path)
    if im.mode != "RGB":
        im = im.convert("RGB")
    return im


@curried
def Image_draw_rectangle(im, x, y, w, h, c):
    im2 = im.copy()
    d = Draw(im2)
    d.rectangle((x, y, x + w, y + h), c)
    return im2


@curried
def Image_copy(im):
    return im.copy()


@curried
def Image_crop(im, x, y, w, h):
    return im.crop((x, y, x + w, y + h))


@curried
def Image_resize(im, w, h):
    return im.resize((w, h), _lanczos_resample())


@curried
def Image_fit_inside(im, max_w, max_h):
    """Resize preserving aspect ratio to fit within max_w × max_h (PIL thumbnail semantics)."""
    im2 = im.copy()
    im2.thumbnail((max_w, max_h), _lanczos_resample())
    return im2


@curried
def Image_rotate(im, angle):
    return im.rotate(float(angle), expand=False)


@curried
def Image_flip_horizontal(im):
    return im.transpose(_transpose_flip_lr())


@curried
def Image_flip_vertical(im):
    return im.transpose(_transpose_flip_tb())


@curried
def Image_get_pixel(im, x, y):
    r, g, b = im.getpixel((x, y))
    return ("Color_mk", r, g, b)


@curried
def Image_put_pixel(im, x, y, color):
    im2 = im.copy()
    im2.putpixel((x, y), tuple(color[1:]))
    return im2


@curried
def Image_paste(dest, src, x, y):
    out = dest.copy()
    src2 = src if src.mode == out.mode else src.convert(out.mode)
    out.paste(src2, (int(x), int(y)))
    return out


@curried
def Image_grayscale_rgb(im):
    """Luminance convert then back to RGB so downstream Color / drawing stays RGB-sized."""
    return im.convert("L").convert("RGB")


@curried
def Image_invert(im):
    return ImageOps.invert(im)


@curried
def Image_blur(im, radius):
    return im.filter(ImageFilter.GaussianBlur(radius=float(radius)))


@curried
def Image_diff(im1, im2):
    s = sum((a - b) ** 2 for a, b in zip(im1.histogram(), im2.histogram()))
    return math.sqrt(s)


@curried
def Image_diff_mse(im1, im2):
    im1 = np.array(im1)
    im2 = np.array(im2)
    return mse(im1, im2)


_HUGE = 1e30


@curried
def Image_fitness_bw_mse(candidate, reference):
    """MSE on luminance (single channel), lowest when grey tones align."""
    if candidate.size != reference.size:
        return _HUGE
    a = np.asarray(candidate.convert("L"), dtype=np.float64)
    b = np.asarray(reference.convert("L"), dtype=np.float64)
    return float(np.mean((a - b) ** 2))


@curried
def Image_fitness_half_size_mse(candidate, reference):
    """MSE on luminance after resizing both images to half width and height (floor)."""
    if candidate.size != reference.size:
        return _HUGE
    w, h = candidate.size
    w2, h2 = max(1, w // 2), max(1, h // 2)
    a = np.asarray(candidate.resize((w2, h2)).convert("L"), dtype=np.float64)
    b = np.asarray(reference.resize((w2, h2)).convert("L"), dtype=np.float64)
    return float(np.mean((a - b) ** 2))


@curried
def Image_fitness_row_mismatch(candidate, reference):
    """Number of horizontal scanlines that differ from the reference anywhere on that row."""
    if candidate.size != reference.size:
        return _HUGE
    a = np.asarray(candidate.convert("RGB"))
    b = np.asarray(reference.convert("RGB"))
    bad_rows = np.any(a != b, axis=(1, 2))
    return float(np.sum(bad_rows))


@curried
def Image_fitness_col_mismatch(candidate, reference):
    """Number of vertical columns that differ from the reference anywhere on that column."""
    if candidate.size != reference.size:
        return _HUGE
    a = np.asarray(candidate.convert("RGB"))
    b = np.asarray(reference.convert("RGB"))
    bad_cols = np.any(a != b, axis=(0, 2))
    return float(np.sum(bad_cols))


@curried
def Image_fitness_pixel_mismatch(candidate, reference):
    """Number of pixels whose RGB triple differs from the reference."""
    if candidate.size != reference.size:
        return _HUGE
    a = np.asarray(candidate.convert("RGB"))
    b = np.asarray(reference.convert("RGB"))
    diff_px = np.any(a != b, axis=2)
    return float(np.sum(diff_px))
