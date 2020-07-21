from .annotation import aefunction, aedocumentation

import numpy as np
from PIL import Image, ImageDraw

''' Image binds in Aeon to Python '''

@aefunction("""type Image {
    width : Integer;
    height : Integer;
}""")
class AeonImage(object):
    def __init__(self):
        pass

@aefunction("""type ImageDraw {
    img : Image;
}""")
class AeonImageDraw(object):
    def __init__(self):
        pass

@aefunction("""type ColorInt as {x:Integer | x >= 0 && x <= 255};""")
class ColorInt(object):
    def __init__(self):
        pass

@aefunction("""type Color {
    a : ColorInt;
    b : ColorInt;
    c : ColorInt;
}""")
class Color(object):
    def __init__(self):
        pass

@aefunction("""type Coordinate {
    x : Integer;
    y : Integer;
}""")
class Coordinate(object):
    def __init__(self):
        pass

@aefunction('load_image(path : String) -> Image;')
def load_image(path):
    return Image.open(path)

@aefunction('create_image(width:{width:Integer | width > 0}, height:{height:Integer | height > 0}) -> {i:Image | i.width == width && i.height == height};')
def create_image(x, y):
    return Image.new('RGB', (x, y), color='white')

@aefunction('create_draw(i : Image) -> ImageDraw;')
def image_draw(img):
    return ImageDraw.Draw(img.copy())

@aefunction('make_color(a:ColorInt, b:ColorInt, c:ColorInt) -> {color:Color | color.a == a && color.b == b && color.c == c};')
def make_color(a, b, c):
    return (a, b, c)

@aefunction("""make_coordinate(img:Image, x0:{x0:Integer | x0 >= 0 && x0 <= img.width}, y0:{y0:Integer | y0 >= 0 && y0 <= img.height},
                                          x1:{x1:Integer | x1 >= 0 && x1 <= img.width}, y1:{y1:Integer | y1 >= 0 && y1 <= img.height}) -> {c:Coordinate | c.x == x && c.y == y};""")
def make_coordinate(x0, y0, x1, y1):
    return [x0, y0, x1, y1]

@aefunction('draw_rectangle(i : ImageDraw, coordinate : Coordinate, color : Color) -> ImageDraw;')
def draw_rectangle(imgdraw, coord, color):
    imgdraw = imgdraw.copy()
    imgdraw.rectangle(coord, fill=color)
    return imgdraw

@aefunction('image_diff(i1 : Image, i2 : Image) -> Double;')
def image_diff(img1, img2):
    return np.sum(np.fabs(np.subtract(img2[:], img1[:])))

@aefunction('show_image(i : ImageDraw) -> Image;')
def show_image(imgdraw):
    imgdraw = imgdraw.copy()
    imgdraw.show()
    return imgdraw

@aefunction('save_image(i : Image, name : String) -> Boolean;')
def save_image(img, path):
    img.save(path)
    return True
