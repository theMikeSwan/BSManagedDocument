//
//  BSManagedDocument.m
//
//  Created by Sasmito Adibowo on 29-08-12.
//  Rewritten by Mike Abdullah on 02-11-12.
//  Copyright (c) 2012-2013 Karelia Software, Basil Salad Software. All rights reserved.
//  http://basilsalad.com
//
//  Licensed under the BSD License <http://www.opensource.org/licenses/bsd-license>
//  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY
//  EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
//  OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT
//  SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
//  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED
//  TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR
//  BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
//  STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
//  THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
//

#import "BSManagedDocument.h"

#import <objc/message.h>

NSString* BSManagedDocumentDidSaveNotification = @"BSManagedDocumentDidSaveNotification" ;

@interface BSManagedDocument ()
@property(nonatomic, copy) NSURL *autosavedContentsTempDirectoryURL;
@end


@implementation BSManagedDocument

#pragma mark UIManagedDocument-inspired methods

+ (NSString *)storeContentName; { return @"StoreContent"; }
+ (NSString *)persistentStoreName; { return @"persistentStore"; }

+ (NSString *)storePathForDocumentPath:(NSString*)path
{
    BOOL isDirectory = YES;
    [[NSFileManager defaultManager] fileExistsAtPath:path
                                         isDirectory:&isDirectory];
    /* I added the initialization YES on 20180114 after seeing a runtime
     warning here, sayig that isDirectory had a "Load of value -96,
     which is not a valid value for type 'BOOL' (aka 'signed char')". */
    if (isDirectory)
    {
        /* path is a file package. */
        path = [path stringByAppendingPathComponent:[BSManagedDocument storeContentName]];
        path = [path stringByAppendingPathComponent:[BSManagedDocument persistentStoreName]];
    }

    return path;
}

+ (NSString *)documentPathForStorePath:(NSString*)path
                     documentExtension:(NSString*)extension
{
    NSString* answer = nil;
    if ([[path pathExtension] isEqualToString:extension])
    {
        answer = path;
    }
    else if ([[path lastPathComponent] isEqualToString:[self persistentStoreName]]) {
        path = [path stringByDeletingLastPathComponent];
        if ([[path lastPathComponent] isEqualToString:[self storeContentName]]) {
            path = [path stringByDeletingLastPathComponent];
            if ([[path pathExtension] isEqualToString:extension]) {
                answer = path;
            }
        }
    }

    return answer;
}


+ (NSURL *)persistentStoreURLForDocumentURL:(NSURL *)fileURL;
{
    NSString *storeContent = [self storeContentName];
    if (storeContent) fileURL = [fileURL URLByAppendingPathComponent:storeContent];
    
    fileURL = [fileURL URLByAppendingPathComponent:[self persistentStoreName]];
    return fileURL;
}

- (NSManagedObjectContext *)managedObjectContext;
{
    if (!_managedObjectContext)
    {
        NSManagedObjectContext *context = [[self.class.managedObjectContextClass alloc] initWithConcurrencyType:NSMainQueueConcurrencyType];
        if(context.undoManager == nil) {
            context.undoManager = [[NSUndoManager alloc] init];
        }
        
        [self setManagedObjectContext:context];
    }
    
    return _managedObjectContext;
}

- (void)setManagedObjectContext:(NSManagedObjectContext *)context;
{
    // Setup the rest of the stack for the context

    NSPersistentStoreCoordinator *coordinator = [[NSPersistentStoreCoordinator alloc] initWithManagedObjectModel:[self managedObjectModel]];
    
    NSManagedObjectContext *parentContext = [[self.class.managedObjectContextClass alloc] initWithConcurrencyType:NSPrivateQueueConcurrencyType];
    parentContext.undoManager = nil; // no point in it supporting undo
    parentContext.persistentStoreCoordinator = coordinator;
    
    [context setParentContext:parentContext];

    _managedObjectContext = context;
    
    [super setUndoManager:[context undoManager]]; // has to be super as we implement -setUndoManager: to be a no-op
    // See note JK20170624 at end of file
}

// Having this method is a bit of a hack for Sandvox's benefit. I intend to remove it in favour of something neater
+ (Class)managedObjectContextClass; { return [NSManagedObjectContext class]; }

- (NSManagedObjectModel *)managedObjectModel;
{
    if (!_managedObjectModel)
    {
        _managedObjectModel = [NSManagedObjectModel mergedModelFromBundles:[NSArray arrayWithObject:[NSBundle mainBundle]]];
    }

    return _managedObjectModel;
}

- (BOOL)configurePersistentStoreCoordinatorForURL:(NSURL *)storeURL
                                           ofType:(NSString *)fileType
                               modelConfiguration:(NSString *)configuration
                                     storeOptions:(NSDictionary *)storeOptions
                                            error:(NSError **)error_p
{
    /* I was getting a crash on launch, in OS X 10.11, when previously-opened
     document was attempted to be reopened (for "state restoration") by
     -[NSDocumentController reopenDocumentForURL:withContentsOfURL:display:completionHandler:],
     if said document could not be migrated because it was of an unsupported
     previous data model version.  (Yes, this is an edge edge case).
     This happened in two different projects of mine, one ARC, one non-ARC.
     The crashing seemed to be fixed after I introduced the following local
     'error' variable to isolate it from the out NSError**.
     Jerry Krinock 2016-Mar-14. */
    NSError* __block error = nil ;
    NSManagedObjectContext *context = self.managedObjectContext;

    // Adding a persistent store will post a notification. If your app already has an
    // NSObjectController (or subclass) setup to the context, it will react to that notification,
    // on the assumption it's posted on the main thread. That could do some very weird things, so
    // let's make sure the notification is actually posted on the main thread.
    // Also seems to fix the deadlock in https://github.com/karelia/BSManagedDocument/issues/36
    if ([context respondsToSelector:@selector(performBlockAndWait:)])
    {
        [context performBlockAndWait:^{
            NSPersistentStoreCoordinator *storeCoordinator = context.persistentStoreCoordinator;

            _store = [storeCoordinator addPersistentStoreWithType:[self persistentStoreTypeForFileType:fileType]
                                                    configuration:configuration
                                                              URL:storeURL
                                                          options:storeOptions
                                                            error:&error];
        }];
    }
    else {
        NSPersistentStoreCoordinator *storeCoordinator = context.persistentStoreCoordinator;

        _store = [storeCoordinator addPersistentStoreWithType:[self persistentStoreTypeForFileType:fileType]
                                                configuration:configuration
                                                          URL:storeURL
                                                      options:storeOptions
                                                        error:&error];
    }
    
    if (error && error_p)
    {
        *error_p = error;
    }

    return (_store != nil);
}

- (BOOL)configurePersistentStoreCoordinatorForURL:(NSURL *)storeURL
                                           ofType:(NSString *)fileType
                                            error:(NSError **)error
{
    // On 10.8+, the coordinator whinges but doesn't fail if you leave out NSReadOnlyPersistentStoreOption and the file turns out to be read-only. Supplying a value makes it fail with a (not very helpful) error when the store is read-only
    BOOL readonly = [self isInViewingMode];
    
    NSDictionary *options = @{
                              // For apps linked against 10.9+ and supporting 10.6 still, use the old
                              // style journal. Since the journal lives alongside the persistent store
                              // I figure there's a chance it could be copied from a new Mac to an old one
                              // https://developer.apple.com/library/mac/releasenotes/DataManagement/WhatsNew_CoreData_OSX/index.html
#if MAC_OS_X_VERSION_MAX_ALLOWED >= MAC_OS_X_VERSION_10_9 && MAC_OS_X_VERSION_MIN_REQUIRED <= MAC_OS_X_VERSION_10_6
                              NSSQLitePragmasOption : @{ @"journal_mode" : @"DELETE" },
#endif
                              
                              NSReadOnlyPersistentStoreOption : @(readonly)
                              };

    return [self configurePersistentStoreCoordinatorForURL:storeURL
                                                    ofType:fileType
                                        modelConfiguration:nil
                                              storeOptions:options
                                                     error:error];
}

- (NSString *)persistentStoreTypeForFileType:(NSString *)fileType { return NSSQLiteStoreType; }

- (BOOL)readAdditionalContentFromURL:(NSURL *)absoluteURL error:(NSError **)error; { return YES; }

- (id)additionalContentForURL:(NSURL *)absoluteURL saveOperation:(NSSaveOperationType)saveOperation error:(NSError **)error;
{
	// Need to hand back something so as not to indicate there was an error
    return [NSNull null];
}

- (BOOL)writeAdditionalContent:(id)content toURL:(NSURL *)absoluteURL originalContentsURL:(NSURL *)absoluteOriginalContentsURL error:(NSError **)error;
{
    return YES;
}

#pragma mark Core Data-Specific

- (BOOL)updateMetadataForPersistentStore:(NSPersistentStore *)store error:(NSError **)error;
{
    return YES;
}

#pragma mark Lifecycle

- (void)close;
{
    [super close];
    [self deleteAutosavedContentsTempDirectory];
}

#pragma mark Reading Document Data

- (BOOL)readFromURL:(NSURL *)absoluteURL ofType:(NSString *)typeName error:(NSError **)outError
{
    // Preflight the URL
    //  A) If the file happens not to exist for some reason, Core Data unhelpfully gives "invalid file name" as the error. NSURL gives better descriptions
    //  B) When reverting a document, the persistent store will already have been removed by the time we try adding the new one (see below). If adding the new store fails that most likely leaves us stranded with no store, so it's preferable to catch errors before removing the store if possible
    if (![absoluteURL checkResourceIsReachableAndReturnError:outError]) return NO;
    
    
    // If have already read, then this is a revert-type affair, so must reload data from disk
    if (_store)
    {
        if (!([NSThread isMainThread])) {
            [NSException raise:NSInternalInconsistencyException format:@"%@: I didn't anticipate reverting on a background thread!", NSStringFromSelector(_cmd)];
        }
        
        // NSPersistentDocument states: "Revert resets the document’s managed object context. Objects are subsequently loaded from the persistent store on demand, as with opening a new document."
        // I've found for atomic stores that -reset only rolls back to the last loaded or saved version of the store; NOT what's actually on disk
        // To force it to re-read from disk, the only solution I've found is removing and re-adding the persistent store
        NSManagedObjectContext *context = self.managedObjectContext;
        
            // In my testing, HAVE to do the removal using parent's private queue. Otherwise, it deadlocks, trying to acquire a _PFLock
            NSManagedObjectContext *parent = context.parentContext;
            while (parent)
            {
                context = parent;   parent = context.parentContext;
            }
            
            __block BOOL result;
            [context performBlockAndWait:^{
                result = [context.persistentStoreCoordinator removePersistentStore:_store error:outError];
            }];

        _store = nil;
    }
    
    
    // Setup the store
    // If the store happens not to exist, because the document is corrupt or in the wrong format, -configurePersistentStoreCoordinatorForURL:… will create a placeholder file which is likely undesirable! The only way to avoid that that I can see is to preflight the URL. Possible race condition, but not in any truly harmful way
    NSURL *storeURL = [[self class] persistentStoreURLForDocumentURL:absoluteURL];
    if (![storeURL checkResourceIsReachableAndReturnError:outError])
    {
        // The document architecture presents such an error as "file doesn't exist", which makes no sense to the user, so customize it
        if (outError && [*outError code] == NSFileReadNoSuchFileError && [[*outError domain] isEqualToString:NSCocoaErrorDomain])
        {
            *outError = [NSError errorWithDomain:NSCocoaErrorDomain
                                            code:NSFileReadCorruptFileError
                                        userInfo:@{ NSUnderlyingErrorKey : *outError }];
        }
        
        return NO;
    }
    
    BOOL result = [self configurePersistentStoreCoordinatorForURL:storeURL
                                                           ofType:typeName
                                                            error:outError];
    
    if (result)
    {
        result = [self readAdditionalContentFromURL:absoluteURL error:outError];
    }
    
    return result;
}

#pragma mark Writing Document Data

- (id)contentsForURL:(NSURL *)url ofType:(NSString *)typeName saveOperation:(NSSaveOperationType)saveOperation error:(NSError **)outError;
{
    // NSAssert([NSThread isMainThread], @"Somehow -%@ has been called off of the main thread (operation %u to: %@)", NSStringFromSelector(_cmd), (unsigned)saveOperation, [url path]);
    // See Note JK20180125 below.
    
    // Grab additional content that a subclass might provide
    if (outError) *outError = nil;  // unusually for me, be forgiving of subclasses which forget to fill in the error
    id additionalContent = [self additionalContentForURL:url saveOperation:saveOperation error:outError];
    if (!additionalContent)
    {
        if (outError) NSAssert(*outError != nil, @"-additionalContentForURL:saveOperation:error: failed with a nil error");
        return nil;
    }
    
    
    // Save the main context, ready for parent to be saved in a moment
    NSManagedObjectContext *context = self.managedObjectContext;
    if (![context save:outError]) return nil;
    
    
    // What we consider to be "contents" is actually a worker block
    BOOL (^contents)(NSURL *, NSSaveOperationType, NSURL *, NSError**) = ^(NSURL *url, NSSaveOperationType saveOperation, NSURL *originalContentsURL, NSError **error) {
        
        // For the first save of a document, create the folders on disk before we do anything else
        // Then setup persistent store appropriately
        BOOL result = YES;
        NSURL *storeURL = [self.class persistentStoreURLForDocumentURL:url];
        
        if (!_store)
        {
            result = [self createPackageDirectoriesAtURL:url
                                                  ofType:typeName
                                        forSaveOperation:saveOperation
                                     originalContentsURL:originalContentsURL
                                                   error:error];
            if (!result) return NO;
            
            result = [self configurePersistentStoreCoordinatorForURL:storeURL
                                                              ofType:typeName
                                                               error:error];
            if (!result) return NO;
        }
        else if (saveOperation == NSSaveAsOperation)
        {
            // Copy the whole package to the new location, not just the store content
            // -writeStoreContent… routine will adjust store URL for us
            if (![self writeBackupToURL:url error:error])
            {
                return NO;
            }
        }
        else
        {
            if (self.class.autosavesInPlace)
            {
                if (saveOperation == NSAutosaveElsewhereOperation)
                {
                    // Special-case autosave-elsewhere for 10.7+ documents that have been saved
                    // e.g. reverting a doc that has unautosaved changes
                    // The system asks us to autosave it to some temp location before closing
                    // CAN'T save-in-place to achieve that, since the doc system is expecting us to leave the original doc untouched, ready to load up as the "reverted" version
                    // But the doc system also asks to do this when performing a Save As operation, and choosing to discard unsaved edits to the existing doc. In which case the SQLite store moves out underneath us and we blow up shortly after
                    // Doc system apparently considers it fine to fail at this, since it passes in NULL as the error pointer
                    // With great sadness and wretchedness, that's the best workaround I have for the moment
                    NSURL *fileURL = self.fileURL;
                    if (fileURL)
                    {
                        NSURL *autosaveURL = self.autosavedContentsFileURL;
                        if (!autosaveURL)
                        {
                            // Make a copy of the existing doc to a location we control first
                            NSURL *autosaveTempDirectory = self.autosavedContentsTempDirectoryURL;
                            NSAssert(autosaveTempDirectory == nil, @"Somehow have a temp directory, but no knowledge of a doc inside it");
                            
                            autosaveTempDirectory = [[NSFileManager defaultManager] URLForDirectory:NSItemReplacementDirectory
                                                                                           inDomain:NSUserDomainMask
                                                                                  appropriateForURL:fileURL
                                                                                             create:YES
                                                                                              error:error];
                            if (!autosaveTempDirectory) return NO;
                            self.autosavedContentsTempDirectoryURL = autosaveTempDirectory;
                            
                            autosaveURL = [autosaveTempDirectory URLByAppendingPathComponent:fileURL.lastPathComponent];
                            if (![self writeBackupToURL:autosaveURL error:error]) return NO;
                            
                            self.autosavedContentsFileURL = autosaveURL;
                        }
                        
                        // Bring the autosaved doc up-to-date
                        result = [self writeStoreContentToURL:[self.class persistentStoreURLForDocumentURL:autosaveURL]
                                                        error:error];
                        if (!result) return NO;
                        
                        result = [self writeAdditionalContent:additionalContent
                                                        toURL:autosaveURL
                                          originalContentsURL:originalContentsURL
                                                        error:error];
                        if (!result) return NO;
                        
                        
                        // Then copy that across to the final URL
                        return [self writeBackupToURL:url error:error];
                    }
                }
            }
            else
            {
                if (saveOperation != NSSaveOperation && saveOperation != NSAutosaveInPlaceOperation)
                {
                    if (![storeURL checkResourceIsReachableAndReturnError:NULL])
                    {
                        result = [self createPackageDirectoriesAtURL:url
                                                              ofType:typeName
                                                    forSaveOperation:saveOperation
                                                 originalContentsURL:originalContentsURL
                                                               error:error];
                        if (!result) return NO;
                        
                        // Fake a placeholder file ready for the store to save over
                        if (![[NSData data] writeToURL:storeURL options:0 error:error]) return NO;
                    }
                }
            }
        }
        
        
        // Right, let's get on with it!
        if (![self writeStoreContentToURL:storeURL error:error]) return NO;
        
            result = [self writeAdditionalContent:additionalContent toURL:url originalContentsURL:originalContentsURL error:error];
            
            if (result)
            {
                // Update package's mod date. Two circumstances where this is needed:
                //  user requests a save when there's no changes; SQLite store doesn't bother to touch the disk in which case
                //  saving where +storeContentName is non-nil; that folder's mod date updates, but the overall package needs prompting
                // Seems simplest to just apply this logic all the time
                NSError *error;
                if (![url setResourceValue:[NSDate date] forKey:NSURLContentModificationDateKey error:&error])
                {
                    NSLog(@"Updating package mod date failed: %@", error);  // not critical, so just log it
                }
            }
        
        
        // Restore persistent store URL after Save To-type operations. Even if save failed (just to be on the safe side)
        if (saveOperation == NSSaveToOperation)
        {
            if (![[_store persistentStoreCoordinator] setURL:originalContentsURL forPersistentStore:_store])
            {
                NSLog(@"Failed to reset store URL after Save To Operation");
            }
        }
        
        
        return result;
    };
    
    return [contents copy];
}

- (BOOL)createPackageDirectoriesAtURL:(NSURL *)url
                               ofType:(NSString *)typeName
                     forSaveOperation:(NSSaveOperationType)saveOperation
                  originalContentsURL:(NSURL *)originalContentsURL
                                error:(NSError **)error;
{
    // Create overall package
    NSDictionary *attributes = [self fileAttributesToWriteToURL:url
                                                         ofType:typeName
                                               forSaveOperation:saveOperation
                                            originalContentsURL:originalContentsURL
                                                          error:error];
    if (!attributes) return NO;
    
    BOOL result = [[NSFileManager defaultManager] createDirectoryAtPath:[url path]
                                            withIntermediateDirectories:NO
                                                             attributes:attributes
                                                                  error:error];
    if (!result) return NO;
    
    // Create store content folder too
    NSString *storeContent = self.class.storeContentName;
    if (storeContent)
    {
        NSURL *storeContentURL = [url URLByAppendingPathComponent:storeContent];
        
        result = [[NSFileManager defaultManager] createDirectoryAtPath:[storeContentURL path]
                                           withIntermediateDirectories:NO
                                                            attributes:attributes
                                                                 error:error];
        if (!result) return NO;
    }
    
    // Set the bundle bit for good measure, so that docs won't appear as folders on Macs without your app installed. Don't care if it fails
    [self setBundleBitForDirectoryAtURL:url];
    
    return YES;
}

- (void)saveToURL:(NSURL *)url ofType:(NSString *)typeName forSaveOperation:(NSSaveOperationType)saveOperation completionHandler:(void (^)(NSError *))completionHandler
{
    // Can't touch _additionalContent etc. until existing save has finished
    // At first glance, -performActivityWithSynchronousWaiting:usingBlock: seems the right way to do that. But turns out:
    //  * super is documented to use -performAsynchronousFileAccessUsingBlock: internally
    //  * Autosaving (as tested on 10.7) is declared to the system as *file access*, rather than an *activity*, so a regular save won't block the UI waiting for autosave to finish
    //  * If autosaving while quitting, calling -performActivity… here results in deadlock
    [self performAsynchronousFileAccessUsingBlock:^(void (^fileAccessCompletionHandler)(void)) {
        
        NSAssert(_contents == nil, @"Can't begin save; another is already in progress. Perhaps you forgot to wrap the call inside of -performActivityWithSynchronousWaiting:usingBlock:");
        
        
        // Stash contents temporarily into an ivar so -writeToURL:… can access it from the worker thread
        NSError *error = nil ;
        _contents = [self contentsForURL:url ofType:typeName saveOperation:saveOperation error:&error];
        
        if (!_contents)
        {
            // The docs say "be sure to invoke super", but by my understanding it's fine not to if it's because of a failure, as the filesystem hasn't been touched yet.
            fileAccessCompletionHandler();
            if (completionHandler) completionHandler(error);
            return;
        }
        
        
        // Kick off async saving work
        [super saveToURL:url ofType:typeName forSaveOperation:saveOperation completionHandler:^(NSError *error) {
            
            // If the save failed, it might be an error the user can recover from.
			// e.g. the dreaded "file modified by another application"
			// NSDocument handles this by presenting the error, which includes recovery options
			// If the user does choose to Save Anyway, the doc system leaps straight onto secondary thread to
			// accomplish it, without calling this method again.
			// Thus we want to hang onto _contents until the overall save operation is finished, rather than
			// just this method. The best way I can see to do that is to make the cleanup its own activity, so
			// it runs after the end of the current one. Unfortunately there's no guarantee anyone's been
            // thoughtful enough to register this as an activity (autosave, I'm looking at you), so only rely
            // on it if there actually is a recoverable error
			if ([error recoveryAttempter])
            {
                [self performActivityWithSynchronousWaiting:NO usingBlock:^(void (^activityCompletionHandler)(void)) {
                    
                    _contents = nil;
                    
                    dispatch_async(dispatch_get_main_queue(), ^{
                        activityCompletionHandler();
                    });
                }];
            }
            else
            {
                _contents = nil;
            }
			
			
            // Clean up our custom autosaved contents directory if appropriate
            if (!error &&
                (saveOperation == NSSaveOperation || saveOperation == NSAutosaveInPlaceOperation || saveOperation == NSSaveAsOperation))
            {
                [self deleteAutosavedContentsTempDirectory];
            }
            
			
			// And can finally declare we're done
            dispatch_async(dispatch_get_main_queue(), ^{
                fileAccessCompletionHandler();
                if (completionHandler) completionHandler(error);
            });
        }];
    }];
}


#if MAC_OS_X_VERSION_MAX_ALLOWED < 101300
/* Documentation says that this method was deprecated in macOS 10.7, but I did
 not get any compiler warnings until compiling with 10.13 SDK.  Oh, well; the
 above #if is to avoid the warning. */
- (BOOL)saveToURL:(NSURL *)url ofType:(NSString *)typeName forSaveOperation:(NSSaveOperationType)saveOperation error:(NSError **)outError;
{
    BOOL result = [super saveToURL:url ofType:typeName forSaveOperation:saveOperation error:outError];
    
    if (result &&
        (saveOperation == NSSaveOperation || saveOperation == NSAutosaveInPlaceOperation || saveOperation == NSSaveAsOperation))
    {
        [self deleteAutosavedContentsTempDirectory];
    }
    
    return result;
}
#endif

/*	Regular Save operations can write directly to the existing document since Core Data provides atomicity for us
 */
- (BOOL)writeSafelyToURL:(NSURL *)absoluteURL
				  ofType:(NSString *)typeName
		forSaveOperation:(NSSaveOperationType)saveOperation
				   error:(NSError **)outError
{
    BOOL result = NO ;
    BOOL done = NO ;

    // It's possible subclassers support more file types than the Core Data package-based one
    // BSManagedDocument supplies. e.g. an alternative format for exporting, say. If so, they don't
    // want our custom logic kicking in when writing it, so test for that as best we can.
    // https://github.com/karelia/BSManagedDocument/issues/36#issuecomment-91773320
	if ([NSWorkspace.sharedWorkspace type:self.fileType conformsToType:typeName]) {
        
		// At this point, we've either captured all document content, or are writing on the main thread, so it's fine to unblock the UI
		[self unblockUserInteraction];
		
		
        if (saveOperation == NSSaveOperation || saveOperation == NSAutosaveInPlaceOperation ||
            (saveOperation == NSAutosaveElsewhereOperation && [absoluteURL isEqual:[self autosavedContentsFileURL]]))
        {
            NSURL *backupURL = nil;
            
			// As of 10.8, need to make a backup of the document when saving in-place
			// Unfortunately, it turns out 10.7 includes -backupFileURL, just that it's private. Checking AppKit number seems to be our best bet
			if (NSAppKitVersionNumber >= NSAppKitVersionNumber10_8 &&
				[self respondsToSelector:@selector(backupFileURL)] &&
				(saveOperation == NSSaveOperation || saveOperation == NSAutosaveInPlaceOperation) &&
				[[self class] preservesVersions])			// otherwise backupURL has a different meaning
			{
				backupURL = [self backupFileURL];
				if (backupURL)
				{
					if (![self writeBackupToURL:backupURL error:outError])
					{
						// If backup fails, seems it's our responsibility to clean up
						NSError *error;
						if (![[NSFileManager defaultManager] removeItemAtURL:backupURL error:&error])
						{
							NSLog(@"Unable to cleanup after failed backup: %@", error);
						}
						
						return NO;
					}
				}
			}
			
			
            // NSDocument attempts to write a copy of the document out at a temporary location.
            // Core Data cannot support this, so we override it to save directly.
            result = [self writeToURL:absoluteURL
                               ofType:typeName
                     forSaveOperation:saveOperation
                  originalContentsURL:[self fileURL]
                                error:outError];
            
            
            if (!result)
            {
                // Clean up backup if one was made
                // If the failure was actualy NSUserCancelledError thanks to
                // autosaving being implicitly cancellable and a subclass deciding
                // to bail out, this HAS to be done otherwise the doc system will
                // weirdly complain that a file by the same name already exists
                if (backupURL)
                {
                    NSError *error;
                    if (![[NSFileManager defaultManager] removeItemAtURL:backupURL error:&error])
                    {
                        NSLog(@"Unable to remove backup after failed write: %@", error);
                    }
                }
                
                // The -write… method maybe wasn't to know that it's writing to the live document, so might have modified it. #179730
                // We can patch up a bit by updating modification date so user doesn't get baffling document-edited warnings again!
                NSDate *modDate;
                if ([absoluteURL getResourceValue:&modDate forKey:NSURLContentModificationDateKey error:NULL])
                {
                    if (modDate)    // some file systems don't support mod date
                    {
                        [self setFileModificationDate:modDate];
                    }
                }
            }
            
            done = YES;
        }
    }
    
    if (!done) {
        // Other situations are basically fine to go through the regular channels
        result = [super writeSafelyToURL:absoluteURL
                                  ofType:typeName
                        forSaveOperation:saveOperation
                                   error:outError];
    }
    
    if (result) {
        NSNotification* note = [[NSNotification alloc] initWithName:BSManagedDocumentDidSaveNotification
                                                             object:self
                                                           userInfo:nil] ;
        [[NSNotificationCenter defaultCenter] performSelectorOnMainThread:@selector(postNotification:)
                                                               withObject:note
                                                            waitUntilDone:NO] ;
    }
    
    return result ;
}

- (BOOL)writeBackupToURL:(NSURL *)backupURL error:(NSError **)outError;
{
    NSURL *source = self.mostRecentlySavedFileURL;
    /* The following also copies any additional content in the package. */
	return [[NSFileManager defaultManager] copyItemAtURL:source toURL:backupURL error:outError];
}

- (BOOL)writeToURL:(NSURL *)inURL
            ofType:(NSString *)typeName
  forSaveOperation:(NSSaveOperationType)saveOp
originalContentsURL:(NSURL *)originalContentsURL
             error:(NSError **)error
{
    // Grab additional content before proceeding. This should *only* happen when writing entirely on the main thread
    // (e.g. Using one of the old synchronous -save… APIs. Note: duplicating a document calls -writeSafely… directly)
    // To have gotten here on any thread but the main one is a programming error and unworkable, so we throw an exception
    if (!_contents)
    {
		_contents = [self contentsForURL:inURL ofType:typeName saveOperation:saveOp error:error];
        if (!_contents) return NO;
        
        // Worried that _contents hasn't been retained? Never fear, we'll set it straight back to nil before exiting this method, I promise
        
        
        // And now we're ready to write for real
        BOOL result = [self writeToURL:inURL ofType:typeName forSaveOperation:saveOp originalContentsURL:originalContentsURL error:error];
        
        
        // Finish up. Don't worry, _additionalContent was never retained on this codepath, so doesn't need to be released
        _contents = nil;
        return result;
    }
    
    
    // We implement contents as a block which is called to perform the writing
    BOOL (^contentsBlock)(NSURL *, NSSaveOperationType, NSURL *, NSError**) = _contents;
    return contentsBlock(inURL, saveOp, originalContentsURL, error);
}

- (void)setBundleBitForDirectoryAtURL:(NSURL *)url;
{
    NSError *error;
    if (![url setResourceValue:@YES forKey:NSURLIsPackageKey error:&error])
    {
        NSLog(@"Error marking document as a package: %@", error);
    }
}

- (BOOL)writeStoreContentToURL:(NSURL *)storeURL error:(NSError **)error;
{
    // First update metadata
    __block BOOL result = [self updateMetadataForPersistentStore:_store error:error];
    if (!result) return NO;
    
    
    // On 10.6 saving is just one call, all on main thread. 10.7+ have to work on the context's private queue
    NSManagedObjectContext *context = [self managedObjectContext];
    
        [self unblockUserInteraction];
        
        NSManagedObjectContext *parent = [context parentContext];
        
        [parent performBlockAndWait:^{
            result = [self preflightURL:storeURL thenSaveContext:parent error:error];
        }];
    
    return result;
}

- (BOOL)preflightURL:(NSURL *)storeURL thenSaveContext:(NSManagedObjectContext *)context error:(NSError **)error;
{
    // Preflight the save since it tends to crash upon failure pre-Mountain Lion. rdar://problem/10609036
    // Could use this code on 10.7+:
    //NSNumber *writable;
    //result = [URL getResourceValue:&writable forKey:NSURLIsWritableKey error:&error];
    
    if ([[NSFileManager defaultManager] isWritableFileAtPath:[storeURL path]])
    {
        // Ensure store is saving to right location
        if ([context.persistentStoreCoordinator setURL:storeURL forPersistentStore:_store])
        {
            return [context save:error];
        }
    }
    
    if (error)
    {
        // Generic error. Doc/error system takes care of supplying a nice generic message to go with it
        *error = [NSError errorWithDomain:NSCocoaErrorDomain code:NSFileWriteNoPermissionError userInfo:nil];
    }
    
    return NO;
}

#pragma mark NSDocument

+ (BOOL)canConcurrentlyReadDocumentsOfType:(NSString *)typeName { return YES; }

- (BOOL)isEntireFileLoaded { return NO; }

- (BOOL)canAsynchronouslyWriteToURL:(NSURL *)url ofType:(NSString *)typeName forSaveOperation:(NSSaveOperationType)saveOperation {
    return YES;
}

- (void)setFileURL:(NSURL *)absoluteURL
{
    // Mark persistent store as moved
    if (![self autosavedContentsFileURL])
    {
        [self setURLForPersistentStoreUsingFileURL:absoluteURL];
    }
    
    [super setFileURL:absoluteURL];
}

- (void)setURLForPersistentStoreUsingFileURL:(NSURL *)absoluteURL;
{
    if (!_store) return;
    
    NSPersistentStoreCoordinator *coordinator = [[self managedObjectContext] persistentStoreCoordinator];
    
    NSURL *storeURL = [[self class] persistentStoreURLForDocumentURL:absoluteURL];
    
    if (![coordinator setURL:storeURL forPersistentStore:_store])
    {
        NSLog(@"Unable to set store URL");
    }
}

#pragma mark Autosave

- (void)setAutosavedContentsFileURL:(NSURL *)absoluteURL;
{
    [super setAutosavedContentsFileURL:absoluteURL];
    
    // Point the store towards the most recent known URL
    absoluteURL = [self mostRecentlySavedFileURL];
    if (absoluteURL) [self setURLForPersistentStoreUsingFileURL:absoluteURL];
}

- (NSURL *)mostRecentlySavedFileURL;
{
    // Before the user chooses where to place a new document, it has an autosaved URL only
    // On 10.6-, autosaves save newer versions of the document *separate* from the original doc
    NSURL *result = [self autosavedContentsFileURL];
    if (!result) result = [self fileURL];
    return result;
}

/*
 When asked to autosave an existing doc elsewhere, we do so via an
 intermedate, temporary copy of the doc. This code tracks that temp folder
 so it can be deleted when no longer in use.
 */

@synthesize autosavedContentsTempDirectoryURL = _autosavedContentsTempDirectoryURL;

- (void)deleteAutosavedContentsTempDirectory;
{
    NSURL *autosaveTempDir = self.autosavedContentsTempDirectoryURL;
    if (autosaveTempDir)
    {
        self.autosavedContentsTempDirectoryURL = nil;
        
        NSError *error;
        if (![[NSFileManager defaultManager] removeItemAtURL:autosaveTempDir error:&error])
        {
            NSLog(@"Unable to remove temporary directory: %@", error);
        }
    }
}

#pragma mark Reverting Documents

- (BOOL)revertToContentsOfURL:(NSURL *)absoluteURL ofType:(NSString *)typeName error:(NSError **)outError;
{
    // Tear down old windows. Wrap in an autorelease pool to get us much torn down before the reversion as we can
    @autoreleasepool
    {
    NSArray *controllers = [[self windowControllers] copy]; // we're sometimes handed underlying mutable array. #156271
    for (NSWindowController *aController in controllers)
    {
        [self removeWindowController:aController];
        [aController close];
    }
    }


    @try
    {
        if (![super revertToContentsOfURL:absoluteURL ofType:typeName error:outError]) return NO;
        [self deleteAutosavedContentsTempDirectory];
        
        return YES;
    }
    @finally
    {
        [self makeWindowControllers];
        
        // Don't show the new windows if in the middle of reverting due to the user closing document
        // and choosing to revert changes. The new window bouncing on screen looks wrong, and then
        // stops the document closing properly (or at least appearing to have closed).
        // In theory I could not bother recreating the window controllers either. But the document
        // system seems to have the expectation that it can keep your document instance around in
        // memory after the revert-and-close, ready to re-use later (e.g. the user asks to open the
        // doc again). If that happens, the window controllers need to still exist, ready to be
        // shown.
        if (!_closing) [self showWindows];
    }
}

- (void)canCloseDocumentWithDelegate:(id)delegate shouldCloseSelector:(SEL)shouldCloseSelector contextInfo:(void *)contextInfo {
    // Track if in the middle of closing
    _closing = YES;
    
    void (^completionHandler)(BOOL) = ^(BOOL shouldClose) {
        if (delegate) {
//<<<<<<< HEAD
//            typedef void (*callback_type)(id, SEL, id, BOOL, void*);
//            callback_type callback = (callback_type)objc_msgSend;
//            callback(delegate, shouldCloseSelector, self, shouldClose, contextInfo);
//=======
            /* Calls to objc_msgSend()  won't compile, by default, or projects
             "upgraded" by Xcode 8-9, due to fact that Build Setting
             "Enable strict checking of objc_msgSend Calls" is now ON.  See
             https://stackoverflow.com/questions/24922913/too-many-arguments-to-function-call-expected-0-have-3
             The result is, oddly, a Semantic Issue:
             "Too many arguments to function call, expected 0, have 5"
             I chose the answer by Sahil Kapoor, which allows me to leave
             the Build Setting ON and not fight with future Xcode updates. */
            id (*typed_msgSend)(id, SEL, id, BOOL, void*) = (void *)objc_msgSend;
            typed_msgSend(delegate, shouldCloseSelector, self, shouldClose, contextInfo);
//>>>>>>> jer
        }
    };
    
    /*
     There may be a bug near here, or it may be in Veris 7:
     Click in menu: File > New Subject.
     Click the red 'Close' button.
     Next line will deadlock.
     Sending [self setChangeCount:NSChangeCleared] before that line does not help.
     To get rid of such a document (which will reappear on any subsequent launch
     due to state restoration), send here [self close].
     */
    [super canCloseDocumentWithDelegate:self
                    shouldCloseSelector:@selector(document:didDecideToClose:contextInfo:)
                            contextInfo:Block_copy((__bridge void *)completionHandler)];
}

- (void)document:(NSDocument *)document didDecideToClose:(BOOL)shouldClose contextInfo:(void *)contextInfo {
    _closing = NO;
    
    // Pass on to original delegate
    void (^completionHandler)(BOOL) = (__bridge void (^)(BOOL))(contextInfo);
    completionHandler(shouldClose);
    Block_release(contextInfo);
}

#pragma mark Duplicating Documents

- (NSDocument *)duplicateAndReturnError:(NSError **)outError;
{
    // If the doc is brand new, have to force the autosave to write to disk
    if (!self.fileURL && !self.autosavedContentsFileURL && !self.hasUnautosavedChanges)
    {
        [self updateChangeCount:NSChangeDone];
        NSDocument *result = [self duplicateAndReturnError:outError];
        [self updateChangeCount:NSChangeUndone];
        return result;
    }
    
    
    // Make sure copy on disk is up-to-date
    if (![self fakeSynchronousAutosaveAndReturnError:outError]) return nil;
    
    
    // Let super handle the overall duplication so it gets the window-handling
    // right. But use custom writing logic that actually copies the existing doc
    BOOL (^contentsBlock)(NSURL*, NSSaveOperationType, NSURL*, NSError**) = ^(NSURL *url, NSSaveOperationType saveOperation, NSURL *originalContentsURL, NSError **error) {
        return [self writeBackupToURL:url error:error];
    };
    
    _contents = contentsBlock;
    NSDocument *result = [super duplicateAndReturnError:outError];
    _contents = nil;
    
    return result;
}

/*  Approximates a synchronous version of -autosaveDocumentWithDelegate:didAutosaveSelector:contextInfo:    */
- (BOOL)fakeSynchronousAutosaveAndReturnError:(NSError **)outError;
{
    // Kick off an autosave
    __block BOOL result = YES;
    [self autosaveWithImplicitCancellability:NO completionHandler:^(NSError *errorOrNil) {
        if (errorOrNil)
        {
            result = NO;
            *outError = [errorOrNil copy];  // in case there's an autorelease pool
        }
    }];
    
    // Somewhat of a hack: wait for autosave to finish
    [self performSynchronousFileAccessUsingBlock:^{ }];
    
    return result;
}

// See note JK20170624 at end of file

#pragma mark Error Presentation

/*! we override willPresentError: here largely to deal with
 any validation issues when saving the document
 */
- (NSError *)willPresentError:(NSError *)inError
{
	NSError *result = nil;
    
    // customizations for NSCocoaErrorDomain
	if ( [[inError domain] isEqualToString:NSCocoaErrorDomain] )
	{
		NSInteger errorCode = [inError code];
		
		// is this a Core Data validation error?
		if ( (NSValidationErrorMinimum <= errorCode) && (errorCode <= NSValidationErrorMaximum) )
		{
			// If there are multiple validation errors, inError will be a NSValidationMultipleErrorsError
			// and all the validation errors will be in an array in the userInfo dictionary for key NSDetailedErrorsKey
			NSArray *detailedErrors = [[inError userInfo] objectForKey:NSDetailedErrorsKey];
			if ( detailedErrors != nil )
			{
				NSUInteger numErrors = [detailedErrors count];
				NSMutableString *errorString = [NSMutableString stringWithFormat:@"%lu validation errors have occurred.", (unsigned long)numErrors];
				NSMutableString *secondary = [NSMutableString string];
				if ( numErrors > 3 )
				{
					[secondary appendString:NSLocalizedString(@"The first 3 are:\n", @"To be followed by 3 error messages")];
				}
				
				NSUInteger i;
				for ( i = 0; i < ((numErrors > 3) ? 3 : numErrors); i++ )
				{
					[secondary appendFormat:@"%@\n", [[detailedErrors objectAtIndex:i] localizedDescription]];
				}
				
				NSMutableDictionary *userInfo = [NSMutableDictionary dictionaryWithDictionary:[inError userInfo]];
				[userInfo setObject:errorString forKey:NSLocalizedDescriptionKey];
				[userInfo setObject:secondary forKey:NSLocalizedRecoverySuggestionErrorKey];
                
				result = [NSError errorWithDomain:[inError domain] code:[inError code] userInfo:userInfo];
			}
		}
	}
    
	// for errors we didn't customize, call super, passing the original error
	if ( !result )
	{
		result = [super willPresentError:inError];
	}
    
    return result;
}

@end

/* Note JK20170624

 I removed code in two places which purportedly sets the document's undo
 manager as NSPersistentDocument does.  The code I removed creates a managed
 object context, which initially has nil undo manager, then later copies its
 nil undo manager to the document.  Result: document has nil undo manager.
 Furthermore, it overrides the document's -setUndoManager: to be a noop,
 making it impossible to set a non-nil undo manager later.

 I have not fully tested this in a demo project, although in one project
 (Veris) it seems to give a nil undo manager, as my analysis predicts.
 In any case, it is possibly not compatible with my requirement in another
 project (BkmkMgrs) of using Graham Cox' GCUndoManager instead of
 NSUndoManager.

 And I do not believe that the code I removed simply behaves the same as
 NSPersistentDocument, because my BkmkMgrs app had an non-nil undo manager
 before I simply replaced NSPersistentDocument with out-of-the-box
 BSManagedDocument.

 Jerry Krinock  2017-06-24
 */

/* Note JK20180125

 I've removed the above assertion because it tripped for me when I had
 enabled asynchronous saving, and I think it is a false alarm.  The call
 stack was as shown below.  Indeed it was on a secondary thread, because
 the main thread invoked
 -[BkmxDoc writeSafelyToURL:ofType:forSaveOperation:error:], which the
 system called on a secondary thread.  Is that not the whole idea of
 asynchronous saving?  For macOS 10.7+, this class does return YES for
 -canAsynchronouslyWriteToURL:::.

 Thread 50 Queue : com.apple.root.default-qos (concurrent)
 #0    0x00007fff57c3823f in -[NSAssertionHandler handleFailureInMethod:object:file:lineNumber:description:] ()
 #1    0x00000001002b7e13 in -[BSManagedDocument contentsForURL:ofType:saveOperation:error:] at /Users/jk/Documents/Programming/Projects/BSManagedDocument/BSManagedDocument.m:396
 #2    0x00000001002b9881 in -[BSManagedDocument writeToURL:ofType:forSaveOperation:originalContentsURL:error:] at /Users/jk/Documents/Programming/Projects/BSManagedDocument/BSManagedDocument.m:872
 #3    0x00000001002b95da in -[BSManagedDocument writeSafelyToURL:ofType:forSaveOperation:error:] at /Users/jk/Documents/Programming/Projects/BSManagedDocument/BSManagedDocument.m:791
 #4    0x00000001002e0d41 in -[BkmxDoc writeSafelyToURL:ofType:forSaveOperation:error:] at /Users/jk/Documents/Programming/Projects/BkmkMgrs/BkmxDoc.m:5383
 #5    0x00007fff53c39294 in __85-[NSDocument(NSDocumentSaving) _saveToURL:ofType:forSaveOperation:completionHandler:]_block_invoke_2.1146 ()
 #6    0x0000000100887c3d in _dispatch_call_block_and_release ()
 #7    0x000000010087fd1f in _dispatch_client_callout ()
 #8    0x000000010088dba8 in _dispatch_queue_override_invoke ()
 #9    0x0000000100881b76 in _dispatch_root_queue_drain ()
 #10    0x000000010088184f in _dispatch_worker_thread3 ()
 #11    0x00000001008fc1c2 in _pthread_wqthread ()
 #12    0x00000001008fbc45 in start_wqthread ()
 Enqueued from com.apple.main-thread (Thread 1) Queue : com.apple.main-thread (serial)
 #0    0x0000000100896669 in _dispatch_root_queue_push_override ()
 #1    0x00007fff53c3916f in __85-[NSDocument(NSDocumentSaving) _saveToURL:ofType:forSaveOperation:completionHandler:]_block_invoke.1143 ()
 #2    0x00007fff535b2918 in __68-[NSDocument _errorForOverwrittenFileWithSandboxExtension:andSaver:]_block_invoke_2.1097 ()
 #3    0x00007fff57de36c1 in __110-[NSFileCoordinator(NSPrivate) _coordinateReadingItemAtURL:options:writingItemAtURL:options:error:byAccessor:]_block_invoke.448 ()
 #4    0x00007fff57de2657 in -[NSFileCoordinator(NSPrivate) _withAccessArbiter:invokeAccessor:orDont:andRelinquishAccessClaim:] ()
 #5    0x00007fff57de32cb in -[NSFileCoordinator(NSPrivate) _coordinateReadingItemAtURL:options:writingItemAtURL:options:error:byAccessor:] ()
 #6    0x00007fff53c34954 in -[NSDocument(NSDocumentSaving) _fileCoordinator:coordinateReadingContentsAndWritingItemAtURL:byAccessor:] ()
 #7    0x00007fff53c34b62 in -[NSDocument(NSDocumentSaving) _coordinateReadingContentsAndWritingItemAtURL:byAccessor:] ()
 #8    0x00007fff535b2860 in __68-[NSDocument _errorForOverwrittenFileWithSandboxExtension:andSaver:]_block_invoke.1096 ()
 #9    0x00007fff53674eb4 in -[NSDocument(NSDocumentSerializationAPIs) continueFileAccessUsingBlock:] ()
 #10    0x00007fff5367688a in __62-[NSDocument(NSDocumentSerializationAPIs) _performFileAccess:]_block_invoke.354 ()
 #11    0x00007fff535f38c0 in __62-[NSDocumentController(NSInternal) _onMainThreadInvokeWorker:]_block_invoke.2153 ()
 #12    0x00007fff55acc58c in __CFRUNLOOP_IS_CALLING_OUT_TO_A_BLOCK__ ()
 #13    0x00007fff55aaf043 in __CFRunLoopDoBlocks ()
 #14    0x00007fff55aae6ce in __CFRunLoopRun ()
 #15    0x00007fff55aadf43 in CFRunLoopRunSpecific ()
 #16    0x00007fff54dc5e26 in RunCurrentEventLoopInMode ()
 #17    0x00007fff54dc5b96 in ReceiveNextEventCommon ()
 #18    0x00007fff54dc5914 in _BlockUntilNextEventMatchingListInModeWithFilter ()
 #19    0x00007fff53090f5f in _DPSNextEvent ()
 #20    0x00007fff53826b4c in -[NSApplication(NSEvent) _nextEventMatchingEventMask:untilDate:inMode:dequeue:] ()
 #21    0x00007fff53085d6d in -[NSApplication run] ()
 #22    0x00007fff53054f1a in NSApplicationMain ()
 #23    0x00000001000014bc in main at /Users/jk/Documents/Programming/Projects/BkmkMgrs/Bkmx-Main.m:83
 #24    0x00007fff7d3c1115 in start ()
*/
