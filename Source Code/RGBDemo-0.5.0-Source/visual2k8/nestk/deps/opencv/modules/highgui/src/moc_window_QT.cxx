/****************************************************************************
** Meta object code from reading C++ file 'window_QT.h'
**
** Created: Sun Jun 12 17:31:49 2011
**      by: The Qt Meta Object Compiler version 62 (Qt 4.7.1)
**
** WARNING! All changes made in this file will be lost!
*****************************************************************************/

#include "../../../../../../../nestk/deps/opencv/modules/highgui/src/window_QT.h"
#if !defined(Q_MOC_OUTPUT_REVISION)
#error "The header file 'window_QT.h' doesn't include <QObject>."
#elif Q_MOC_OUTPUT_REVISION != 62
#error "This file was generated using the moc from 4.7.1. It"
#error "cannot be used with the include files from this version of Qt."
#error "(The moc has changed too much.)"
#endif

QT_BEGIN_MOC_NAMESPACE
static const uint qt_meta_data_GuiReceiver[] = {

 // content:
       5,       // revision
       0,       // classname
       0,    0, // classinfo
      24,   14, // methods
       0,    0, // properties
       0,    0, // enums/sets
       0,    0, // constructors
       0,       // flags
       0,       // signalCount

 // slots: signature, parameters, type, tag, flags
      24,   13,   12,   12, 0x0a,
      55,   50,   12,   12, 0x2a,
      77,   50,   12,   12, 0x0a,
     100,   12,   12,   12, 0x0a,
     167,  119,   12,   12, 0x0a,
     267,  210,   12,   12, 0x0a,
     326,  317,   12,   12, 0x0a,
     372,  354,   12,   12, 0x0a,
     411,  402,   12,   12, 0x0a,
     454,  436,   12,   12, 0x0a,
     487,  436,   12,   12, 0x0a,
     525,   12,   12,   12, 0x0a,
     535,   13,   12,   12, 0x0a,
     575,   50,  568,   12, 0x0a,
     597,   50,  568,   12, 0x0a,
     620,   13,   12,   12, 0x0a,
     650,   50,  568,   12, 0x0a,
     684,  674,   12,   12, 0x0a,
     715,   50,   12,   12, 0x0a,
     745,   50,   12,   12, 0x0a,
     827,  775,   12,   12, 0x0a,
     906,  887,   12,   12, 0x0a,
    1006,  942,   12,   12, 0x0a,
    1045,   12,   12,   12, 0x0a,

       0        // eod
};

static const char qt_meta_stringdata_GuiReceiver[] = {
    "GuiReceiver\0\0name,flags\0"
    "createWindow(QString,int)\0name\0"
    "createWindow(QString)\0destroyWindow(QString)\0"
    "destroyAllWindow()\0"
    "trackbar_name,window_name,value,count,on_change\0"
    "addSlider(QString,QString,void*,int,void*)\0"
    "trackbar_name,window_name,value,count,on_change,userdata\0"
    "addSlider2(QString,QString,void*,int,void*,void*)\0"
    "name,x,y\0moveWindow(QString,int,int)\0"
    "name,width,height\0resizeWindow(QString,int,int)\0"
    "name,arr\0showImage(QString,void*)\0"
    "name,text,delayms\0displayInfo(QString,QString,int)\0"
    "displayStatusBar(QString,QString,int)\0"
    "timeOut()\0toggleFullScreen(QString,double)\0"
    "double\0isFullScreen(QString)\0"
    "getPropWindow(QString)\0"
    "setPropWindow(QString,double)\0"
    "getRatioWindow(QString)\0name,arg2\0"
    "setRatioWindow(QString,double)\0"
    "saveWindowParameters(QString)\0"
    "loadWindowParameters(QString)\0"
    "window_name,callbackOpenGL,userdata,angle,zmin,zmax\0"
    "setOpenGLCallback(QString,void*,void*,double,double,double)\0"
    "arg1,text,org,font\0"
    "putText(void*,QString,QPoint,void*)\0"
    "button_name,button_type,initial_button_state,on_change,userdata\0"
    "addButton(QString,int,int,void*,void*)\0"
    "enablePropertiesButtonEachWindow()\0"
};

const QMetaObject GuiReceiver::staticMetaObject = {
    { &QObject::staticMetaObject, qt_meta_stringdata_GuiReceiver,
      qt_meta_data_GuiReceiver, 0 }
};

#ifdef Q_NO_DATA_RELOCATION
const QMetaObject &GuiReceiver::getStaticMetaObject() { return staticMetaObject; }
#endif //Q_NO_DATA_RELOCATION

const QMetaObject *GuiReceiver::metaObject() const
{
    return QObject::d_ptr->metaObject ? QObject::d_ptr->metaObject : &staticMetaObject;
}

void *GuiReceiver::qt_metacast(const char *_clname)
{
    if (!_clname) return 0;
    if (!strcmp(_clname, qt_meta_stringdata_GuiReceiver))
        return static_cast<void*>(const_cast< GuiReceiver*>(this));
    return QObject::qt_metacast(_clname);
}

int GuiReceiver::qt_metacall(QMetaObject::Call _c, int _id, void **_a)
{
    _id = QObject::qt_metacall(_c, _id, _a);
    if (_id < 0)
        return _id;
    if (_c == QMetaObject::InvokeMetaMethod) {
        switch (_id) {
        case 0: createWindow((*reinterpret_cast< QString(*)>(_a[1])),(*reinterpret_cast< int(*)>(_a[2]))); break;
        case 1: createWindow((*reinterpret_cast< QString(*)>(_a[1]))); break;
        case 2: destroyWindow((*reinterpret_cast< QString(*)>(_a[1]))); break;
        case 3: destroyAllWindow(); break;
        case 4: addSlider((*reinterpret_cast< QString(*)>(_a[1])),(*reinterpret_cast< QString(*)>(_a[2])),(*reinterpret_cast< void*(*)>(_a[3])),(*reinterpret_cast< int(*)>(_a[4])),(*reinterpret_cast< void*(*)>(_a[5]))); break;
        case 5: addSlider2((*reinterpret_cast< QString(*)>(_a[1])),(*reinterpret_cast< QString(*)>(_a[2])),(*reinterpret_cast< void*(*)>(_a[3])),(*reinterpret_cast< int(*)>(_a[4])),(*reinterpret_cast< void*(*)>(_a[5])),(*reinterpret_cast< void*(*)>(_a[6]))); break;
        case 6: moveWindow((*reinterpret_cast< QString(*)>(_a[1])),(*reinterpret_cast< int(*)>(_a[2])),(*reinterpret_cast< int(*)>(_a[3]))); break;
        case 7: resizeWindow((*reinterpret_cast< QString(*)>(_a[1])),(*reinterpret_cast< int(*)>(_a[2])),(*reinterpret_cast< int(*)>(_a[3]))); break;
        case 8: showImage((*reinterpret_cast< QString(*)>(_a[1])),(*reinterpret_cast< void*(*)>(_a[2]))); break;
        case 9: displayInfo((*reinterpret_cast< QString(*)>(_a[1])),(*reinterpret_cast< QString(*)>(_a[2])),(*reinterpret_cast< int(*)>(_a[3]))); break;
        case 10: displayStatusBar((*reinterpret_cast< QString(*)>(_a[1])),(*reinterpret_cast< QString(*)>(_a[2])),(*reinterpret_cast< int(*)>(_a[3]))); break;
        case 11: timeOut(); break;
        case 12: toggleFullScreen((*reinterpret_cast< QString(*)>(_a[1])),(*reinterpret_cast< double(*)>(_a[2]))); break;
        case 13: { double _r = isFullScreen((*reinterpret_cast< QString(*)>(_a[1])));
            if (_a[0]) *reinterpret_cast< double*>(_a[0]) = _r; }  break;
        case 14: { double _r = getPropWindow((*reinterpret_cast< QString(*)>(_a[1])));
            if (_a[0]) *reinterpret_cast< double*>(_a[0]) = _r; }  break;
        case 15: setPropWindow((*reinterpret_cast< QString(*)>(_a[1])),(*reinterpret_cast< double(*)>(_a[2]))); break;
        case 16: { double _r = getRatioWindow((*reinterpret_cast< QString(*)>(_a[1])));
            if (_a[0]) *reinterpret_cast< double*>(_a[0]) = _r; }  break;
        case 17: setRatioWindow((*reinterpret_cast< QString(*)>(_a[1])),(*reinterpret_cast< double(*)>(_a[2]))); break;
        case 18: saveWindowParameters((*reinterpret_cast< QString(*)>(_a[1]))); break;
        case 19: loadWindowParameters((*reinterpret_cast< QString(*)>(_a[1]))); break;
        case 20: setOpenGLCallback((*reinterpret_cast< QString(*)>(_a[1])),(*reinterpret_cast< void*(*)>(_a[2])),(*reinterpret_cast< void*(*)>(_a[3])),(*reinterpret_cast< double(*)>(_a[4])),(*reinterpret_cast< double(*)>(_a[5])),(*reinterpret_cast< double(*)>(_a[6]))); break;
        case 21: putText((*reinterpret_cast< void*(*)>(_a[1])),(*reinterpret_cast< QString(*)>(_a[2])),(*reinterpret_cast< QPoint(*)>(_a[3])),(*reinterpret_cast< void*(*)>(_a[4]))); break;
        case 22: addButton((*reinterpret_cast< QString(*)>(_a[1])),(*reinterpret_cast< int(*)>(_a[2])),(*reinterpret_cast< int(*)>(_a[3])),(*reinterpret_cast< void*(*)>(_a[4])),(*reinterpret_cast< void*(*)>(_a[5]))); break;
        case 23: enablePropertiesButtonEachWindow(); break;
        default: ;
        }
        _id -= 24;
    }
    return _id;
}
static const uint qt_meta_data_CvButtonbar[] = {

 // content:
       5,       // revision
       0,       // classname
       0,    0, // classinfo
       0,    0, // methods
       0,    0, // properties
       0,    0, // enums/sets
       0,    0, // constructors
       0,       // flags
       0,       // signalCount

       0        // eod
};

static const char qt_meta_stringdata_CvButtonbar[] = {
    "CvButtonbar\0"
};

const QMetaObject CvButtonbar::staticMetaObject = {
    { &CvBar::staticMetaObject, qt_meta_stringdata_CvButtonbar,
      qt_meta_data_CvButtonbar, 0 }
};

#ifdef Q_NO_DATA_RELOCATION
const QMetaObject &CvButtonbar::getStaticMetaObject() { return staticMetaObject; }
#endif //Q_NO_DATA_RELOCATION

const QMetaObject *CvButtonbar::metaObject() const
{
    return QObject::d_ptr->metaObject ? QObject::d_ptr->metaObject : &staticMetaObject;
}

void *CvButtonbar::qt_metacast(const char *_clname)
{
    if (!_clname) return 0;
    if (!strcmp(_clname, qt_meta_stringdata_CvButtonbar))
        return static_cast<void*>(const_cast< CvButtonbar*>(this));
    return CvBar::qt_metacast(_clname);
}

int CvButtonbar::qt_metacall(QMetaObject::Call _c, int _id, void **_a)
{
    _id = CvBar::qt_metacall(_c, _id, _a);
    if (_id < 0)
        return _id;
    return _id;
}
static const uint qt_meta_data_CvPushButton[] = {

 // content:
       5,       // revision
       0,       // classname
       0,    0, // classinfo
       1,   14, // methods
       0,    0, // properties
       0,    0, // enums/sets
       0,    0, // constructors
       0,       // flags
       0,       // signalCount

 // slots: signature, parameters, type, tag, flags
      14,   13,   13,   13, 0x08,

       0        // eod
};

static const char qt_meta_stringdata_CvPushButton[] = {
    "CvPushButton\0\0callCallBack(bool)\0"
};

const QMetaObject CvPushButton::staticMetaObject = {
    { &QPushButton::staticMetaObject, qt_meta_stringdata_CvPushButton,
      qt_meta_data_CvPushButton, 0 }
};

#ifdef Q_NO_DATA_RELOCATION
const QMetaObject &CvPushButton::getStaticMetaObject() { return staticMetaObject; }
#endif //Q_NO_DATA_RELOCATION

const QMetaObject *CvPushButton::metaObject() const
{
    return QObject::d_ptr->metaObject ? QObject::d_ptr->metaObject : &staticMetaObject;
}

void *CvPushButton::qt_metacast(const char *_clname)
{
    if (!_clname) return 0;
    if (!strcmp(_clname, qt_meta_stringdata_CvPushButton))
        return static_cast<void*>(const_cast< CvPushButton*>(this));
    return QPushButton::qt_metacast(_clname);
}

int CvPushButton::qt_metacall(QMetaObject::Call _c, int _id, void **_a)
{
    _id = QPushButton::qt_metacall(_c, _id, _a);
    if (_id < 0)
        return _id;
    if (_c == QMetaObject::InvokeMetaMethod) {
        switch (_id) {
        case 0: callCallBack((*reinterpret_cast< bool(*)>(_a[1]))); break;
        default: ;
        }
        _id -= 1;
    }
    return _id;
}
static const uint qt_meta_data_CvCheckBox[] = {

 // content:
       5,       // revision
       0,       // classname
       0,    0, // classinfo
       1,   14, // methods
       0,    0, // properties
       0,    0, // enums/sets
       0,    0, // constructors
       0,       // flags
       0,       // signalCount

 // slots: signature, parameters, type, tag, flags
      12,   11,   11,   11, 0x08,

       0        // eod
};

static const char qt_meta_stringdata_CvCheckBox[] = {
    "CvCheckBox\0\0callCallBack(bool)\0"
};

const QMetaObject CvCheckBox::staticMetaObject = {
    { &QCheckBox::staticMetaObject, qt_meta_stringdata_CvCheckBox,
      qt_meta_data_CvCheckBox, 0 }
};

#ifdef Q_NO_DATA_RELOCATION
const QMetaObject &CvCheckBox::getStaticMetaObject() { return staticMetaObject; }
#endif //Q_NO_DATA_RELOCATION

const QMetaObject *CvCheckBox::metaObject() const
{
    return QObject::d_ptr->metaObject ? QObject::d_ptr->metaObject : &staticMetaObject;
}

void *CvCheckBox::qt_metacast(const char *_clname)
{
    if (!_clname) return 0;
    if (!strcmp(_clname, qt_meta_stringdata_CvCheckBox))
        return static_cast<void*>(const_cast< CvCheckBox*>(this));
    return QCheckBox::qt_metacast(_clname);
}

int CvCheckBox::qt_metacall(QMetaObject::Call _c, int _id, void **_a)
{
    _id = QCheckBox::qt_metacall(_c, _id, _a);
    if (_id < 0)
        return _id;
    if (_c == QMetaObject::InvokeMetaMethod) {
        switch (_id) {
        case 0: callCallBack((*reinterpret_cast< bool(*)>(_a[1]))); break;
        default: ;
        }
        _id -= 1;
    }
    return _id;
}
static const uint qt_meta_data_CvRadioButton[] = {

 // content:
       5,       // revision
       0,       // classname
       0,    0, // classinfo
       1,   14, // methods
       0,    0, // properties
       0,    0, // enums/sets
       0,    0, // constructors
       0,       // flags
       0,       // signalCount

 // slots: signature, parameters, type, tag, flags
      15,   14,   14,   14, 0x08,

       0        // eod
};

static const char qt_meta_stringdata_CvRadioButton[] = {
    "CvRadioButton\0\0callCallBack(bool)\0"
};

const QMetaObject CvRadioButton::staticMetaObject = {
    { &QRadioButton::staticMetaObject, qt_meta_stringdata_CvRadioButton,
      qt_meta_data_CvRadioButton, 0 }
};

#ifdef Q_NO_DATA_RELOCATION
const QMetaObject &CvRadioButton::getStaticMetaObject() { return staticMetaObject; }
#endif //Q_NO_DATA_RELOCATION

const QMetaObject *CvRadioButton::metaObject() const
{
    return QObject::d_ptr->metaObject ? QObject::d_ptr->metaObject : &staticMetaObject;
}

void *CvRadioButton::qt_metacast(const char *_clname)
{
    if (!_clname) return 0;
    if (!strcmp(_clname, qt_meta_stringdata_CvRadioButton))
        return static_cast<void*>(const_cast< CvRadioButton*>(this));
    return QRadioButton::qt_metacast(_clname);
}

int CvRadioButton::qt_metacall(QMetaObject::Call _c, int _id, void **_a)
{
    _id = QRadioButton::qt_metacall(_c, _id, _a);
    if (_id < 0)
        return _id;
    if (_c == QMetaObject::InvokeMetaMethod) {
        switch (_id) {
        case 0: callCallBack((*reinterpret_cast< bool(*)>(_a[1]))); break;
        default: ;
        }
        _id -= 1;
    }
    return _id;
}
static const uint qt_meta_data_CvTrackbar[] = {

 // content:
       5,       // revision
       0,       // classname
       0,    0, // classinfo
       2,   14, // methods
       0,    0, // properties
       0,    0, // enums/sets
       0,    0, // constructors
       0,       // flags
       0,       // signalCount

 // slots: signature, parameters, type, tag, flags
      12,   11,   11,   11, 0x08,
      35,   27,   11,   11, 0x08,

       0        // eod
};

static const char qt_meta_stringdata_CvTrackbar[] = {
    "CvTrackbar\0\0createDialog()\0myvalue\0"
    "update(int)\0"
};

const QMetaObject CvTrackbar::staticMetaObject = {
    { &CvBar::staticMetaObject, qt_meta_stringdata_CvTrackbar,
      qt_meta_data_CvTrackbar, 0 }
};

#ifdef Q_NO_DATA_RELOCATION
const QMetaObject &CvTrackbar::getStaticMetaObject() { return staticMetaObject; }
#endif //Q_NO_DATA_RELOCATION

const QMetaObject *CvTrackbar::metaObject() const
{
    return QObject::d_ptr->metaObject ? QObject::d_ptr->metaObject : &staticMetaObject;
}

void *CvTrackbar::qt_metacast(const char *_clname)
{
    if (!_clname) return 0;
    if (!strcmp(_clname, qt_meta_stringdata_CvTrackbar))
        return static_cast<void*>(const_cast< CvTrackbar*>(this));
    return CvBar::qt_metacast(_clname);
}

int CvTrackbar::qt_metacall(QMetaObject::Call _c, int _id, void **_a)
{
    _id = CvBar::qt_metacall(_c, _id, _a);
    if (_id < 0)
        return _id;
    if (_c == QMetaObject::InvokeMetaMethod) {
        switch (_id) {
        case 0: createDialog(); break;
        case 1: update((*reinterpret_cast< int(*)>(_a[1]))); break;
        default: ;
        }
        _id -= 2;
    }
    return _id;
}
static const uint qt_meta_data_CvWinProperties[] = {

 // content:
       5,       // revision
       0,       // classname
       0,    0, // classinfo
       0,    0, // methods
       0,    0, // properties
       0,    0, // enums/sets
       0,    0, // constructors
       0,       // flags
       0,       // signalCount

       0        // eod
};

static const char qt_meta_stringdata_CvWinProperties[] = {
    "CvWinProperties\0"
};

const QMetaObject CvWinProperties::staticMetaObject = {
    { &CvWinModel::staticMetaObject, qt_meta_stringdata_CvWinProperties,
      qt_meta_data_CvWinProperties, 0 }
};

#ifdef Q_NO_DATA_RELOCATION
const QMetaObject &CvWinProperties::getStaticMetaObject() { return staticMetaObject; }
#endif //Q_NO_DATA_RELOCATION

const QMetaObject *CvWinProperties::metaObject() const
{
    return QObject::d_ptr->metaObject ? QObject::d_ptr->metaObject : &staticMetaObject;
}

void *CvWinProperties::qt_metacast(const char *_clname)
{
    if (!_clname) return 0;
    if (!strcmp(_clname, qt_meta_stringdata_CvWinProperties))
        return static_cast<void*>(const_cast< CvWinProperties*>(this));
    return CvWinModel::qt_metacast(_clname);
}

int CvWinProperties::qt_metacall(QMetaObject::Call _c, int _id, void **_a)
{
    _id = CvWinModel::qt_metacall(_c, _id, _a);
    if (_id < 0)
        return _id;
    return _id;
}
static const uint qt_meta_data_CvWindow[] = {

 // content:
       5,       // revision
       0,       // classname
       0,    0, // classinfo
       1,   14, // methods
       0,    0, // properties
       0,    0, // enums/sets
       0,    0, // constructors
       0,       // flags
       0,       // signalCount

 // slots: signature, parameters, type, tag, flags
      10,    9,    9,    9, 0x08,

       0        // eod
};

static const char qt_meta_stringdata_CvWindow[] = {
    "CvWindow\0\0displayPropertiesWin()\0"
};

const QMetaObject CvWindow::staticMetaObject = {
    { &CvWinModel::staticMetaObject, qt_meta_stringdata_CvWindow,
      qt_meta_data_CvWindow, 0 }
};

#ifdef Q_NO_DATA_RELOCATION
const QMetaObject &CvWindow::getStaticMetaObject() { return staticMetaObject; }
#endif //Q_NO_DATA_RELOCATION

const QMetaObject *CvWindow::metaObject() const
{
    return QObject::d_ptr->metaObject ? QObject::d_ptr->metaObject : &staticMetaObject;
}

void *CvWindow::qt_metacast(const char *_clname)
{
    if (!_clname) return 0;
    if (!strcmp(_clname, qt_meta_stringdata_CvWindow))
        return static_cast<void*>(const_cast< CvWindow*>(this));
    return CvWinModel::qt_metacast(_clname);
}

int CvWindow::qt_metacall(QMetaObject::Call _c, int _id, void **_a)
{
    _id = CvWinModel::qt_metacall(_c, _id, _a);
    if (_id < 0)
        return _id;
    if (_c == QMetaObject::InvokeMetaMethod) {
        switch (_id) {
        case 0: displayPropertiesWin(); break;
        default: ;
        }
        _id -= 1;
    }
    return _id;
}
static const uint qt_meta_data_ViewPort[] = {

 // content:
       5,       // revision
       0,       // classname
       0,    0, // classinfo
      14,   14, // methods
       0,    0, // properties
       0,    0, // enums/sets
       0,    0, // constructors
       0,       // flags
       0,       // signalCount

 // slots: signature, parameters, type, tag, flags
      29,   10,    9,    9, 0x0a,
      54,    9,    9,    9, 0x0a,
      72,   66,    9,    9, 0x0a,
      90,    9,    9,    9, 0x0a,
     102,    9,    9,    9, 0x0a,
     111,    9,    9,    9, 0x0a,
     121,    9,    9,    9, 0x0a,
     140,    9,    9,    9, 0x0a,
     160,    9,    9,    9, 0x0a,
     177,    9,    9,    9, 0x0a,
     196,    9,    9,    9, 0x0a,
     223,    9,    9,    9, 0x0a,
     240,  234,    9,    9, 0x0a,
     277,    9,    9,    9, 0x08,

       0        // eod
};

static const char qt_meta_stringdata_ViewPort[] = {
    "ViewPort\0\0scaleFactor,center\0"
    "scaleView(qreal,QPointF)\0imgRegion()\0"
    "delta\0moveView(QPointF)\0resetZoom()\0"
    "ZoomIn()\0ZoomOut()\0siftWindowOnLeft()\0"
    "siftWindowOnRight()\0siftWindowOnUp()\0"
    "siftWindowOnDown()\0resizeEvent(QResizeEvent*)\0"
    "saveView()\0event\0contextMenuEvent(QContextMenuEvent*)\0"
    "stopDisplayInfo()\0"
};

const QMetaObject ViewPort::staticMetaObject = {
    { &QGraphicsView::staticMetaObject, qt_meta_stringdata_ViewPort,
      qt_meta_data_ViewPort, 0 }
};

#ifdef Q_NO_DATA_RELOCATION
const QMetaObject &ViewPort::getStaticMetaObject() { return staticMetaObject; }
#endif //Q_NO_DATA_RELOCATION

const QMetaObject *ViewPort::metaObject() const
{
    return QObject::d_ptr->metaObject ? QObject::d_ptr->metaObject : &staticMetaObject;
}

void *ViewPort::qt_metacast(const char *_clname)
{
    if (!_clname) return 0;
    if (!strcmp(_clname, qt_meta_stringdata_ViewPort))
        return static_cast<void*>(const_cast< ViewPort*>(this));
    return QGraphicsView::qt_metacast(_clname);
}

int ViewPort::qt_metacall(QMetaObject::Call _c, int _id, void **_a)
{
    _id = QGraphicsView::qt_metacall(_c, _id, _a);
    if (_id < 0)
        return _id;
    if (_c == QMetaObject::InvokeMetaMethod) {
        switch (_id) {
        case 0: scaleView((*reinterpret_cast< qreal(*)>(_a[1])),(*reinterpret_cast< QPointF(*)>(_a[2]))); break;
        case 1: imgRegion(); break;
        case 2: moveView((*reinterpret_cast< QPointF(*)>(_a[1]))); break;
        case 3: resetZoom(); break;
        case 4: ZoomIn(); break;
        case 5: ZoomOut(); break;
        case 6: siftWindowOnLeft(); break;
        case 7: siftWindowOnRight(); break;
        case 8: siftWindowOnUp(); break;
        case 9: siftWindowOnDown(); break;
        case 10: resizeEvent((*reinterpret_cast< QResizeEvent*(*)>(_a[1]))); break;
        case 11: saveView(); break;
        case 12: contextMenuEvent((*reinterpret_cast< QContextMenuEvent*(*)>(_a[1]))); break;
        case 13: stopDisplayInfo(); break;
        default: ;
        }
        _id -= 14;
    }
    return _id;
}
QT_END_MOC_NAMESPACE
