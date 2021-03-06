/** 
 * @file llfolderview.h
 * @brief Definition of the folder view collection of classes.
 *
 * $LicenseInfo:firstyear=2001&license=viewergpl$
 * 
 * Copyright (c) 2001-2009, Linden Research, Inc.
 * 
 * Second Life Viewer Source Code
 * The source code in this file ("Source Code") is provided by Linden Lab
 * to you under the terms of the GNU General Public License, version 2.0
 * ("GPL"), unless you have obtained a separate licensing agreement
 * ("Other License"), formally executed by you and Linden Lab.  Terms of
 * the GPL can be found in doc/GPL-license.txt in this distribution, or
 * online at http://secondlifegrid.net/programs/open_source/licensing/gplv2
 * 
 * There are special exceptions to the terms and conditions of the GPL as
 * it is applied to this Source Code. View the full text of the exception
 * in the file doc/FLOSS-exception.txt in this software distribution, or
 * online at
 * http://secondlifegrid.net/programs/open_source/licensing/flossexception
 * 
 * By copying, modifying or distributing this software, you acknowledge
 * that you have read and understood your obligations described above,
 * and agree to abide by those obligations.
 * 
 * ALL LINDEN LAB SOURCE CODE IS PROVIDED "AS IS." LINDEN LAB MAKES NO
 * WARRANTIES, EXPRESS, IMPLIED OR OTHERWISE, REGARDING ITS ACCURACY,
 * COMPLETENESS OR PERFORMANCE.
 * $/LicenseInfo$
 */

/**
 *
 * The folder view collection of classes provides an interface for
 * making a 'folder view' similar to the way the a single pane file
 * folder interface works.
 *
 */

#ifndef LL_LLFOLDERVIEW_H
#define LL_LLFOLDERVIEW_H

#include "llfolderviewitem.h"	// because LLFolderView is-a LLFolderViewFolder

#include "lluictrl.h"
#include "v4color.h"
#include "lldarray.h"
#include "stdenums.h"
#include "lldepthstack.h"
#include "lleditmenuhandler.h"
#include "llfontgl.h"
#include "lltooldraganddrop.h"
#include "llviewertexture.h"

class LLFolderViewEventListener;
class LLFolderViewFolder;
class LLFolderViewItem;
class LLInventoryModel;
class LLPanel;
class LLLineEditor;
class LLMenuGL;
class LLScrollableContainerView;
class LLUICtrl;
class LLTextBox;

//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// Class LLFolderView
//
// Th LLFolderView represents the root level folder view object. It
// manages the screen region of the folder view.
//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

class LLUICtrl;
class LLLineEditor;

class LLFolderView : public LLFolderViewFolder, LLEditMenuHandler
{
public:
	typedef void (*SelectCallback)(const std::deque<LLFolderViewItem*> &items, BOOL user_action, void* data);

	static F32 sAutoOpenTime;

	LLFolderView( const std::string& name, LLUIImagePtr root_folder_icon, const LLRect& rect, 
					const LLUUID& source_id, LLView *parent_view );
	virtual ~LLFolderView( void );

	virtual BOOL canFocusChildren() const;

	virtual LLFolderView*	getRoot() { return this; }

	// FolderViews default to sort by name.  This will change that,
	// and resort the items if necessary.
	void setSortOrder(U32 order);
	void checkTreeResortForModelChanged();
	void setFilterPermMask(PermissionMask filter_perm_mask);
	void setSelectCallback(SelectCallback callback, void* user_data) { mSelectCallback = callback, mUserData = user_data; }
	void setAllowMultiSelect(BOOL allow) { mAllowMultiSelect = allow; }

	LLInventoryFilter* getFilter();
	const std::string getFilterSubString(BOOL trim = FALSE);
	bool getFilterWorn() const;
	U32 getFilterTypes() const;
	PermissionMask getFilterPermissions() const;
	// *NOTE: use getFilter()->getShowFolderState();
	//LLInventoryFilter::EFolderShow getShowFolderState();
	U32 getSortOrder() const;
	BOOL isFilterModified();
	BOOL getAllowMultiSelect() { return mAllowMultiSelect; }

	U32 toggleSearchType(std::string toggle);
	U32 getSearchType() const;

	// Close all folders in the view
	void closeAllFolders();
	void openFolder(const std::string& foldername);

	virtual void toggleOpen() {};
	virtual void setOpenArrangeRecursively(BOOL openitem, ERecurseType recurse);
	virtual BOOL addFolder( LLFolderViewFolder* folder);

	// Finds width and height of this object and it's children.  Also
	// makes sure that this view and it's children are the right size.
	virtual S32 arrange( S32* width, S32* height, S32 filter_generation );

	void arrangeAll() { mArrangeGeneration++; }
	S32 getArrangeGeneration() { return mArrangeGeneration; }

	// applies filters to control visibility of inventory items
	virtual void filter( LLInventoryFilter& filter);

	// get the last selected item
	virtual LLFolderViewItem* getCurSelectedItem( void );

	// Record the selected item and pass it down the hierachy.
	virtual BOOL setSelection(LLFolderViewItem* selection, BOOL openitem,
		BOOL take_keyboard_focus);

	// This method is used to toggle the selection of an item. Walks
	// children, and keeps track of selected objects.
	virtual BOOL changeSelection(LLFolderViewItem* selection, BOOL selected);

	virtual void extendSelection(LLFolderViewItem* selection, LLFolderViewItem* last_selected, LLDynamicArray<LLFolderViewItem*>& items);

	virtual BOOL getSelectionList(std::set<LLUUID> &selection);

	// make sure if ancestor is selected, descendents are not
	void sanitizeSelection();
	void clearSelection();
	void addToSelectionList(LLFolderViewItem* item);
	void removeFromSelectionList(LLFolderViewItem* item);

	BOOL startDrag(LLToolDragAndDrop::ESource source);
	void setDragAndDropThisFrame() { mDragAndDropThisFrame = TRUE; }

	// deletion functionality
 	void removeSelectedItems();

	// open the selected item.
	void openSelectedItems( void );
	void propertiesSelectedItems( void );

	void autoOpenItem(LLFolderViewFolder* item);
	void closeAutoOpenedFolders();
	BOOL autoOpenTest(LLFolderViewFolder* item);

	// copy & paste
	virtual void	copy();
	virtual BOOL	canCopy() const;

	virtual void	cut();
	virtual BOOL	canCut() const;

	virtual void	paste();
	virtual BOOL	canPaste() const;

	virtual void	doDelete();
	virtual BOOL	canDoDelete() const;

	// public rename functionality - can only start the process
	void startRenamingSelectedItem( void );

	// These functions were used when there was only one folderview,
	// and relied on that concept. This functionality is now handled
	// by the listeners and the lldraganddroptool.
	//LLFolderViewItem*	getMovingItem() { return mMovingItem; }
	//void setMovingItem( LLFolderViewItem* item ) { mMovingItem = item; }
	//void				dragItemIntoFolder( LLFolderViewItem* moving_item, LLFolderViewFolder* dst_folder, BOOL drop, BOOL* accept );
	//void				dragFolderIntoFolder( LLFolderViewFolder* moving_folder, LLFolderViewFolder* dst_folder, BOOL drop, BOOL* accept );

	// LLUICtrl Functionality
	/*virtual*/ void setFocus(BOOL focus);

	// LLView functionality
	///*virtual*/ BOOL handleKey( KEY key, MASK mask, BOOL called_from_parent );
	/*virtual*/ BOOL handleKeyHere( KEY key, MASK mask );
	/*virtual*/ BOOL handleUnicodeCharHere(llwchar uni_char);
	/*virtual*/ BOOL handleMouseDown( S32 x, S32 y, MASK mask );
	/*virtual*/ BOOL handleDoubleClick( S32 x, S32 y, MASK mask );
	/*virtual*/ BOOL handleRightMouseDown( S32 x, S32 y, MASK mask );
	/*virtual*/ BOOL handleHover( S32 x, S32 y, MASK mask );
	/*virtual*/ BOOL handleDragAndDrop(S32 x, S32 y, MASK mask, BOOL drop,
								   EDragAndDropType cargo_type,
								   void* cargo_data,
								   EAcceptance* accept,
								   std::string& tooltip_msg);
	/*virtual*/ void reshape(S32 width, S32 height, BOOL called_from_parent = TRUE);
	/*virtual*/ void onFocusLost();
	virtual BOOL handleScrollWheel(S32 x, S32 y, S32 clicks);
	virtual void draw();
	virtual void deleteAllChildren();

	void scrollToShowSelection();
	void scrollToShowItem(LLFolderViewItem* item);
	void setScrollContainer( LLScrollableContainerView* parent ) { mScrollContainer = parent; }
	LLRect getVisibleRect();

	BOOL search(LLFolderViewItem* first_item, const std::string &search_string, BOOL backward);
	void setShowSelectionContext(BOOL show) { mShowSelectionContext = show; }
	BOOL getShowSelectionContext();
	void setShowSingleSelection(BOOL show);
	BOOL getShowSingleSelection() { return mShowSingleSelection; }
	F32  getSelectionFadeElapsedTime() { return mMultiSelectionFadeTimer.getElapsedTimeF32(); }

	void addItemID(const LLUUID& id, LLFolderViewItem* itemp);
	void removeItemID(const LLUUID& id);
	LLFolderViewItem* getItemByID(const LLUUID& id);

	void	doIdle();						// Real idle routine
	static void idle(void* user_data);		// static glue to doIdle()

	BOOL needsAutoSelect() { return mNeedsAutoSelect && !mAutoSelectOverride; }
	BOOL needsAutoRename() { return mNeedsAutoRename; }
	void setNeedsAutoRename(BOOL val) { mNeedsAutoRename = val; }

	BOOL getDebugFilters() { return mDebugFilters; }

	// DEBUG only
	void dumpSelectionInformation();

protected:
	LLScrollableContainerView* mScrollContainer;  // NULL if this is not a child of a scroll container.

	static void commitRename( LLUICtrl* renamer, void* user_data );
	static void onRenamerLost( LLUICtrl* renamer, void* user_data);

	void finishRenamingItem( void );
	void closeRenamer( void );

protected:
	LLHandle<LLView>					mPopupMenuHandle;
	
	typedef std::deque<LLFolderViewItem*> selected_items_t;
	selected_items_t				mSelectedItems;
	BOOL							mKeyboardSelection;
	BOOL							mAllowMultiSelect;
	BOOL							mShowFolderHierarchy;
	LLUUID							mSourceID;

	// Renaming variables and methods
	LLFolderViewItem*				mRenameItem;  // The item currently being renamed
	LLLineEditor*					mRenamer;

	BOOL							mNeedsScroll;
	LLFolderViewItem*				mLastScrollItem;
	LLCoordGL						mLastScrollOffset;
	BOOL							mNeedsAutoSelect;
	BOOL							mAutoSelectOverride;
	BOOL							mNeedsAutoRename;
	
	BOOL							mDebugFilters;
	U32								mSortOrder;
	U32								mSearchType;
	LLDepthStack<LLFolderViewFolder>	mAutoOpenItems;
	LLFolderViewFolder*				mAutoOpenCandidate;
	LLFrameTimer					mAutoOpenTimer;
	LLFrameTimer					mSearchTimer;
	std::string						mSearchString;
	LLInventoryFilter*				mFilter;
	BOOL							mShowSelectionContext;
	BOOL							mShowSingleSelection;
	LLFrameTimer					mMultiSelectionFadeTimer;
	S32								mArrangeGeneration;

	void*							mUserData;
	SelectCallback					mSelectCallback;
	S32								mSignalSelectCallback;
	S32								mMinWidth;
	std::map<LLUUID, LLFolderViewItem*> mItemMap;
	BOOL							mDragAndDropThisFrame;

};

bool sort_item_name(LLFolderViewItem* a, LLFolderViewItem* b);
bool sort_item_date(LLFolderViewItem* a, LLFolderViewItem* b);

// Flags for buildContextMenu()
const U32 SUPPRESS_OPEN_ITEM = 0x1;
const U32 FIRST_SELECTED_ITEM = 0x2;

#endif // LL_LLFOLDERVIEW_H
